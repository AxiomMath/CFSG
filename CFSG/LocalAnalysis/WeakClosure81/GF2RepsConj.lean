module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin Subgroup

variable {W : Type*} [CommGroup W]

section Conj

private theorem gf2_Conj_apply_conj (g x : MulAut W) (u : W) :
    x (g u) = g ((g⁻¹ * x * g) u) := by
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]

private theorem gf2_Conj_conj_apply (g x : MulAut W) (u : W) :
    (g * x * g⁻¹) (g u) = g (x u) := by
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]

private theorem gf2_Conj_apply_symm (g x : MulAut W) (w : W) :
    x (g⁻¹ w) = g⁻¹ ((g * x * g⁻¹) w) := by
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]

private theorem gf2_Conj_map_inv {U : Subgroup W} {g : MulAut W} :
    (U.map g.toMonoidHom).map (g⁻¹).toMonoidHom = U := by
  rw [Subgroup.map_map]
  have h : (g⁻¹).toMonoidHom.comp g.toMonoidHom = MonoidHom.id W := by
    ext w
    exact MulEquiv.symm_apply_apply g w
  rw [h, Subgroup.map_id]

private theorem gf2_Conj_map_inv' {U : Subgroup W} {g : MulAut W} :
    (U.map (g⁻¹).toMonoidHom).map g.toMonoidHom = U := by
  rw [Subgroup.map_map]
  have h : g.toMonoidHom.comp (g⁻¹).toMonoidHom = MonoidHom.id W := by
    ext w
    exact MulEquiv.apply_symm_apply g w
  rw [h, Subgroup.map_id]

private theorem gf2_Conj_mem_map_iff (U : Subgroup W) (g : MulAut W) (w : W) :
    g w ∈ U.map g.toMonoidHom ↔ w ∈ U := by
  constructor
  · rintro ⟨u, hu, hgu⟩
    rw [g.injective hgu] at hu
    exact hu
  · intro hw
    exact Subgroup.mem_map.mpr ⟨w, hw, rfl⟩

theorem stableUnder_map_of_normalizes {X : Subgroup (MulAut W)} {g : MulAut W}
    (hg' : ∀ x ∈ X, g⁻¹ * x * g ∈ X) {U : Subgroup W} (hU : StableUnder X U) :
    StableUnder X (U.map g.toMonoidHom) := by
  intro x hx v hv
  rcases Subgroup.mem_map.mp hv with ⟨u, hu, rfl⟩
  refine Subgroup.mem_map.mpr ⟨(g⁻¹ * x * g) u, hU _ (hg' x hx) u hu, ?_⟩
  show g ((g⁻¹ * x * g) u) = x (g u)
  rw [← gf2_Conj_apply_conj]

theorem commSub_map_of_normalizes {X : Subgroup (MulAut W)} {g : MulAut W}
    (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X) (hg' : ∀ x ∈ X, g⁻¹ * x * g ∈ X) (U : Subgroup W) :
    commSub (U.map g.toMonoidHom) X = (commSub U X).map g.toMonoidHom := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨x, hx, w', ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨(g⁻¹ * x * g) w * w⁻¹, ⟨g⁻¹ * x * g, hg' x hx, w, hw, rfl⟩, ?_⟩
    show g ((g⁻¹ * x * g) w * w⁻¹) = x (g w) * (g w)⁻¹
    rw [map_mul, map_inv, ← gf2_Conj_apply_conj]
  · rintro ⟨d, ⟨x, hx, w, hw, rfl⟩, hgd⟩
    rw [← hgd]
    refine ⟨g * x * g⁻¹, hg x hx, g w, ⟨w, hw, rfl⟩, ?_⟩
    show (g * x * g⁻¹) (g w) * (g w)⁻¹ = g (x w * w⁻¹)
    rw [gf2_Conj_conj_apply, map_mul, map_inv]

theorem map_fixV_of_normalizes {X : Subgroup (MulAut W)} {g : MulAut W}
    (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X) (hg' : ∀ x ∈ X, g⁻¹ * x * g ∈ X) :
    (fixV X).map g.toMonoidHom = fixV X := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    intro x hx
    have hv' : ∀ y ∈ X, y v = v := fun y hy => hv y hy
    show x (g v) = g v
    rw [gf2_Conj_apply_conj, hv' (g⁻¹ * x * g) (hg' x hx)]
  · intro hw
    refine Subgroup.mem_map.mpr ⟨g⁻¹ w, ?_, ?_⟩
    · refine mem_fixV.mpr fun x hx => ?_
      have hw' : ∀ y ∈ X, y w = w := fun y hy => hw y hy
      rw [gf2_Conj_apply_symm, hw' (g * x * g⁻¹) (hg x hx)]
    · show g (g⁻¹ w) = w
      exact MulEquiv.apply_symm_apply g w

theorem map_mem_irrSet {X : Subgroup (MulAut W)} {g : MulAut W}
    (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X) (hg' : ∀ x ∈ X, g⁻¹ * x * g ∈ X) {I : Subgroup W}
    (hI : I ∈ irrSet X) : I.map g.toMonoidHom ∈ irrSet X := by
  have hI' : commSub I X = I ∧ IsIrrOn X I (I ⊓ fixV X) := by
    simpa only [irrSet, Set.mem_setOf_eq] using hI
  obtain ⟨hcomm, hIirr⟩ := hI'
  have hfix : (fixV X).map g.toMonoidHom = fixV X := map_fixV_of_normalizes hg hg'
  have hcomm' : commSub (I.map g.toMonoidHom) X = I.map g.toMonoidHom := by
    rw [commSub_map_of_normalizes hg hg' I, hcomm]
  have hinf : I.map g.toMonoidHom ⊓ fixV X = (I ⊓ fixV X).map g.toMonoidHom := by
    rw [show I.map g.toMonoidHom ⊓ fixV X = I.map g.toMonoidHom ⊓ (fixV X).map g.toMonoidHom
      from by rw [hfix]]
    exact (Subgroup.map_inf_eq I (fixV X) g.toMonoidHom g.injective).symm
  have hNlt : I.map g.toMonoidHom ⊓ fixV X < I.map g.toMonoidHom := by
    rw [hinf]
    exact (Subgroup.map_lt_map_iff_of_injective g.injective).mpr hIirr.1
  have hstabI' : StableUnder X (I.map g.toMonoidHom) :=
    stableUnder_map_of_normalizes hg' hIirr.2.1
  have hstabN' : StableUnder X (I.map g.toMonoidHom ⊓ fixV X) := by
    rw [hinf]
    exact stableUnder_map_of_normalizes hg' hIirr.2.2.1
  refine ⟨hcomm', hNlt, hstabI', hstabN', ?_⟩
  intro J' hJ'stab hN'J' hJ'I'
  rw [hinf] at hN'J' ⊢
  have hg'' : ∀ x ∈ X, (g⁻¹)⁻¹ * x * g⁻¹ ∈ X := by
    intro x hx
    simpa using hg x hx
  have hJstab : StableUnder X (J'.map (g⁻¹).toMonoidHom) :=
    stableUnder_map_of_normalizes hg'' hJ'stab
  have hNJ : I ⊓ fixV X ≤ J'.map (g⁻¹).toMonoidHom := by
    have h := Subgroup.map_mono (f := (g⁻¹).toMonoidHom) hN'J'
    rwa [gf2_Conj_map_inv] at h
  have hJI : J'.map (g⁻¹).toMonoidHom ≤ I := by
    have h := Subgroup.map_mono (f := (g⁻¹).toMonoidHom) hJ'I'
    rwa [gf2_Conj_map_inv] at h
  rcases hIirr.2.2.2 (J'.map (g⁻¹).toMonoidHom) hJstab hNJ hJI with hJN | hJI'
  · left
    have h := congrArg (Subgroup.map g.toMonoidHom) hJN
    rwa [gf2_Conj_map_inv'] at h
  · right
    have h := congrArg (Subgroup.map g.toMonoidHom) hJI'
    rwa [gf2_Conj_map_inv'] at h

theorem stableUnder_iSup_of_map_mem {Y : Subgroup (MulAut W)} {S : Set (Subgroup W)}
    (hS : ∀ I ∈ S, ∀ y ∈ Y, I.map y.toMonoidHom ∈ S) : StableUnder Y (⨆ I ∈ S, I) := by
  intro y hy u hu
  have hle : (⨆ I ∈ S, I).map y.toMonoidHom ≤ ⨆ I ∈ S, I := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun I => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hI => le_iSup₂_of_le (I.map y.toMonoidHom) (hS I hI y hy) le_rfl
  exact hle (Subgroup.mem_map.mpr ⟨u, hu, rfl⟩)

theorem stableUnder_iSup_irrSet {Y H : Subgroup (MulAut W)}
    (hn : ∀ y ∈ Y, ∀ h ∈ H, y * h * y⁻¹ ∈ H) : StableUnder Y (⨆ I ∈ irrSet H, I) := by
  refine stableUnder_iSup_of_map_mem fun I hI y hy => ?_
  have hg' : ∀ x ∈ H, y⁻¹ * x * y ∈ H := by
    have h := hn y⁻¹ (Y.inv_mem hy)
    simpa using h
  exact map_mem_irrSet (hn y hy) hg' hI

theorem isIrrOn_sup_fixV {H : Subgroup (MulAut W)} {I : Subgroup W} (hI : I ∈ irrSet H) :
    IsIrrOn H (I ⊔ fixV H) (fixV H) := by
  have hI' : commSub I H = I ∧ IsIrrOn H I (I ⊓ fixV H) := by
    simpa only [irrSet, Set.mem_setOf_eq] using hI
  obtain ⟨_, hIirr⟩ := hI'
  have hFixV : StableUnder H (fixV H) := fun x hx w hw => by
    rw [hw x hx]
    exact hw
  refine ⟨?_, stableUnder_sup hIirr.2.1 hFixV, hFixV, ?_⟩
  · refine lt_of_le_of_ne le_sup_right ?_
    intro h
    exact not_le_fixV_of_mem_irrSet hI (by rw [h]; exact le_sup_left)
  · intro J hJstab hCJ hJIsup
    have hKstab : StableUnder H (J ⊓ I) := stableUnder_inf hJstab hIirr.2.1
    have hNK : I ⊓ fixV H ≤ J ⊓ I := fun z hz => ⟨hCJ hz.2, hz.1⟩
    have hKeq : J = (J ⊓ I) ⊔ fixV H := by
      refine le_antisymm ?_ (sup_le inf_le_left hCJ)
      intro k hk
      obtain ⟨i, hi, c, hc, hik⟩ := Subgroup.mem_sup.mp (hJIsup hk)
      rw [← hik]
      refine Subgroup.mul_mem_sup ⟨?_, hi⟩ hc
      have hik' : i = k * c⁻¹ := by rw [← hik, mul_inv_cancel_right]
      rw [hik']
      exact J.mul_mem hk (J.inv_mem (hCJ hc))
    rcases hIirr.2.2.2 (J ⊓ I) hKstab hNK inf_le_right with hK | hK
    · left
      rw [hKeq, hK]
      exact sup_eq_right.mpr inf_le_right
    · right
      rw [hKeq, hK]

end Conj

section SecIso

theorem secIsoOn_refl {X : Subgroup (MulAut W)} {A A₀ : Subgroup W} (hA : StableUnder X A)
    (hA₀ : StableUnder X A₀) (h : A₀ ≤ A) : SecIsoOn X A A₀ A A₀ := by
  refine ⟨h, h, hA, hA₀, hA, hA₀, A.subtype, ?_, ?_, ?_, ?_⟩
  · intro a
    exact a.2
  · intro a
    rfl
  · intro b hb
    exact ⟨⟨b, hb⟩, by simp⟩
  · intro x hx a a' ha'
    have h1 : (A.subtype a' : W) = x (A.subtype a : W) := ha'
    rw [h1, mul_inv_cancel]
    exact A₀.one_mem

theorem secIsoOn_trans {X : Subgroup (MulAut W)} {A A₀ B B₀ D D₀ : Subgroup W}
    (h₁ : SecIsoOn X A A₀ B B₀) (h₂ : SecIsoOn X B B₀ D D₀) : SecIsoOn X A A₀ D D₀ := by
  obtain ⟨hA₀A, hB₀B, hXA, hXA₀, hXB, hXB₀, β₁, hβ₁B, hβ₁iff, hβ₁surj, hβ₁eq⟩ := h₁
  obtain ⟨_, hD₀D, _, _, hXD, hXD₀, β₂, hβ₂D, hβ₂iff, hβ₂surj, hβ₂eq⟩ := h₂
  refine ⟨hA₀A, hD₀D, hXA, hXA₀, hXD, hXD₀, ?_⟩
  let β₁' : ↥A →* ↥B := β₁.codRestrict B hβ₁B
  let β : ↥A →* W := β₂.comp β₁'
  refine ⟨β, ?_, ?_, ?_, ?_⟩
  · intro a
    exact hβ₂D (β₁' a)
  · intro a
    have key : ((β₁' a : ↥B) : W) ∈ B₀ ↔ ((a : ↥A) : W) ∈ A₀ := hβ₁iff a
    exact (hβ₂iff (β₁' a)).trans key
  · intro d hd
    obtain ⟨b, hb⟩ := hβ₂surj d hd
    obtain ⟨a, ha⟩ := hβ₁surj (b : W) b.2
    refine ⟨a, ?_⟩
    have hmem : ((β₁' a * b⁻¹ : ↥B) : W) ∈ B₀ := by
      have h1 : ((β₁' a * b⁻¹ : ↥B) : W) = β₁ a * (b : W)⁻¹ := by
        dsimp only [β₁']
        rw [Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.codRestrict_apply]
      rw [h1]
      exact ha
    have hD₀₁ : β₂ (β₁' a * b⁻¹) ∈ D₀ := (hβ₂iff (β₁' a * b⁻¹)).mpr hmem
    have hD₀₂ : β₂ b * d⁻¹ ∈ D₀ := hb
    have hβeq : β₂ (β₁' a * b⁻¹) = β a * (β₂ b)⁻¹ := by
      rw [map_mul, map_inv]
      rfl
    have hprod : β a * d⁻¹ = (β a * (β₂ b)⁻¹) * (β₂ b * d⁻¹) := by group
    rw [hprod]
    exact D₀.mul_mem (hβeq ▸ hD₀₁) hD₀₂
  · intro x hx a a' ha'
    let b : ↥B := β₁' a
    let b' : ↥B := β₁' a'
    let b'' : ↥B := ⟨x (β₁ a), hXB x hx (β₁ a) (hβ₁B a)⟩
    have hb'' : (b'' : W) = x (b : W) := rfl
    have hβ₁mem : ((b' * b''⁻¹ : ↥B) : W) ∈ B₀ := by
      have h1 : ((b' * b''⁻¹ : ↥B) : W) = β₁ a' * (x (β₁ a))⁻¹ := by
        dsimp only [b', b'', β₁']
        rw [Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.codRestrict_apply]
      rw [h1]
      exact hβ₁eq x hx a a' ha'
    have hD₀₁ : β₂ b' * (β₂ b'')⁻¹ ∈ D₀ := by
      rw [← map_inv, ← map_mul]
      exact (hβ₂iff (b' * b''⁻¹)).mpr hβ₁mem
    have hD₀₂ : β₂ b'' * (x (β₂ b))⁻¹ ∈ D₀ := hβ₂eq x hx b b'' hb''
    have hgoal : β a' * (x (β a))⁻¹ =
        (β₂ b' * (β₂ b'')⁻¹) * (β₂ b'' * (x (β₂ b))⁻¹) := by
      change β₂ (β₁' a') * (x (β₂ (β₁' a)))⁻¹ =
        (β₂ (β₁' a') * (β₂ b'')⁻¹) * (β₂ b'' * (x (β₂ (β₁' a)))⁻¹)
      group
    rw [hgoal]
    exact D₀.mul_mem hD₀₁ hD₀₂

theorem secIsoOn_map {X : Subgroup (MulAut W)} {g : MulAut W}
    (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X) (hg' : ∀ x ∈ X, g⁻¹ * x * g ∈ X)
    {A A₀ B B₀ : Subgroup W} (h : SecIsoOn X A A₀ B B₀) :
    SecIsoOn X (A.map g.toMonoidHom) (A₀.map g.toMonoidHom) (B.map g.toMonoidHom)
      (B₀.map g.toMonoidHom) := by
  obtain ⟨hA₀A, hB₀B, hXA, hXA₀, hXB, hXB₀, β, hβB, hβiff, hβsurj, hβeq⟩ := h
  refine ⟨Subgroup.map_mono hA₀A, Subgroup.map_mono hB₀B,
    stableUnder_map_of_normalizes hg' hXA, stableUnder_map_of_normalizes hg' hXA₀,
    stableUnder_map_of_normalizes hg' hXB, stableUnder_map_of_normalizes hg' hXB₀, ?_⟩
  let e : ↥A ≃* ↥(A.map g.toMonoidHom) :=
    Subgroup.equivMapOfInjective A g.toMonoidHom g.injective
  let β' : ↥(A.map g.toMonoidHom) →* W := g.toMonoidHom.comp (β.comp e.symm.toMonoidHom)
  have hβ'e : ∀ a : ↥A, β' (e a) = g (β a) := by
    intro a
    show g (β (e.symm (e a))) = g (β a)
    rw [e.symm_apply_apply]
  refine ⟨β', ?_, ?_, ?_, ?_⟩
  · intro u
    have h1 : β' u = g (β (e.symm u)) := by
      conv_lhs => rw [show u = e (e.symm u) from (e.apply_symm_apply u).symm]
      exact hβ'e (e.symm u)
    rw [h1]
    exact Subgroup.mem_map.mpr ⟨β (e.symm u), hβB (e.symm u), rfl⟩
  · intro u
    have h1 : β' u = g (β (e.symm u)) := by
      conv_lhs => rw [show u = e (e.symm u) from (e.apply_symm_apply u).symm]
      exact hβ'e (e.symm u)
    have hu : (u : W) = g ((e.symm u : ↥A) : W) := by
      conv_lhs => rw [show u = e (e.symm u) from (e.apply_symm_apply u).symm]
      exact Subgroup.coe_equivMapOfInjective_apply A g.toMonoidHom g.injective (e.symm u)
    rw [h1, hu]
    exact (gf2_Conj_mem_map_iff B₀ g (β (e.symm u))).trans
      ((hβiff (e.symm u)).trans (gf2_Conj_mem_map_iff A₀ g ((e.symm u : ↥A) : W)).symm)
  · intro b hb
    rcases Subgroup.mem_map.mp hb with ⟨b₀, hb₀, rfl⟩
    obtain ⟨a, ha⟩ := hβsurj b₀ hb₀
    refine ⟨e a, ?_⟩
    show β' (e a) * (g b₀)⁻¹ ∈ B₀.map g.toMonoidHom
    have h2 : β' (e a) * (g b₀)⁻¹ = g (β a * b₀⁻¹) := by
      rw [hβ'e, map_mul, map_inv]
    rw [h2]
    exact Subgroup.mem_map.mpr ⟨β a * b₀⁻¹, ha, rfl⟩
  · intro x hx u u' hu'
    have htu' : β' u' = g (β (e.symm u')) := by
      conv_lhs => rw [show u' = e (e.symm u') from (e.apply_symm_apply u').symm]
      exact hβ'e (e.symm u')
    have htu : β' u = g (β (e.symm u)) := by
      conv_lhs => rw [show u = e (e.symm u) from (e.apply_symm_apply u).symm]
      exact hβ'e (e.symm u)
    have huW : (u : W) = g ((e.symm u : ↥A) : W) := by
      conv_lhs => rw [show u = e (e.symm u) from (e.apply_symm_apply u).symm]
      exact Subgroup.coe_equivMapOfInjective_apply A g.toMonoidHom g.injective (e.symm u)
    have hu'W : (u' : W) = g ((e.symm u' : ↥A) : W) := by
      conv_lhs => rw [show u' = e (e.symm u') from (e.apply_symm_apply u').symm]
      exact Subgroup.coe_equivMapOfInjective_apply A g.toMonoidHom g.injective (e.symm u')
    have hx' : (g⁻¹ * x * g) ∈ X := hg' x hx
    have haa : ((e.symm u' : ↥A) : W) = (g⁻¹ * x * g) ((e.symm u : ↥A) : W) := by
      apply g.injective
      rw [← hu'W, hu', huW, gf2_Conj_apply_conj]
    have hβmem : β (e.symm u') * ((g⁻¹ * x * g) (β (e.symm u)))⁻¹ ∈ B₀ :=
      hβeq (g⁻¹ * x * g) hx' (e.symm u) (e.symm u') haa
    have hgoal : β' u' * (x (β' u))⁻¹ =
        g (β (e.symm u') * ((g⁻¹ * x * g) (β (e.symm u)))⁻¹) := by
      rw [htu', htu, gf2_Conj_apply_conj, ← map_inv, ← map_mul]
    rw [hgoal]
    exact Subgroup.mem_map.mpr
      ⟨β (e.symm u') * ((g⁻¹ * x * g) (β (e.symm u)))⁻¹, hβmem, rfl⟩

end SecIso

end CFSG.LocalAnalysis.WeakClosure81
