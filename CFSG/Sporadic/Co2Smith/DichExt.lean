module

public import CFSG.Sporadic.Co2Smith.DichCompat

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Certificates.ExtraspecialNF

universe u v

namespace LocalConfig

variable (c₁ : LocalConfig.{u}) (c₂ : SmithConfig.{v})

theorem compat_ι_unique {h : c₁.H} {s s' : S0} (hs : c₁.Compat c₂.toLocalConfig h (c₂.ι s))
    (hs' : c₁.Compat c₂.toLocalConfig h (c₂.ι s')) : s = s' := by
  obtain ⟨k, hk, hke⟩ := compat_unique hs hs'
  have h1 : c₂.ι (s⁻¹ * s') ∈ c₂.ι.range ⊓ c₂.E := by
    refine ⟨⟨_, rfl⟩, ?_⟩
    have e : c₂.ι (s⁻¹ * s') = (k : c₂.H) := by rw [map_mul, map_inv, hke]; group
    rw [e]
    exact k.2
  rw [c₂.inf_eq, Subgroup.mem_bot] at h1
  have h2 := c₂.inj (h1.trans (map_one c₂.ι).symm)
  rwa [inv_mul_eq_one] at h2

@[expose] def Shat : Subgroup c₁.H where
  carrier := {h | ∃ s : S0, c₁.Compat c₂.toLocalConfig h (c₂.ι s)}
  mul_mem' := fun ⟨s, hs⟩ ⟨t, ht⟩ => ⟨s * t, by rw [map_mul]; exact hs.mul ht⟩
  one_mem' := ⟨1, by rw [map_one]; exact compat_one⟩
  inv_mem' := fun ⟨s, hs⟩ => ⟨s⁻¹, by rw [map_inv]; exact hs.inv⟩

@[expose] noncomputable def piHat : c₁.Shat c₂ →* S0 where
  toFun h := h.2.choose
  map_one' :=
    c₁.compat_ι_unique c₂ (1 : c₁.Shat c₂).2.choose_spec (by rw [map_one]; exact compat_one)
  map_mul' x y := c₁.compat_ι_unique c₂ (x * y).2.choose_spec (by
    rw [map_mul]
    exact x.2.choose_spec.mul y.2.choose_spec)

theorem piHat_spec (h : c₁.Shat c₂) :
    c₁.Compat c₂.toLocalConfig h (c₂.ι (c₁.piHat c₂ h)) :=
  h.2.choose_spec

theorem piHat_eq {h : c₁.Shat c₂} {s : S0} (hs : c₁.Compat c₂.toLocalConfig h (c₂.ι s)) :
    c₁.piHat c₂ h = s :=
  c₁.compat_ι_unique c₂ (c₁.piHat_spec c₂ h) hs

theorem piHat_surjective :
    Function.Surjective (c₁.piHat c₂) := fun s => by
  obtain ⟨h₁, hh⟩ := exists_compat c₂.toLocalConfig c₁ (c₂.ι s)
  exact ⟨⟨h₁, s, hh.symm⟩, c₁.piHat_eq c₂ hh.symm⟩

theorem piHat_eq_one_iff (h : c₁.Shat c₂) :
    c₁.piHat c₂ h = 1 ↔ ∃ k ∈ Subgroup.center c₁.E, (h : c₁.H) = k := by
  rw [← compat_one_iff (c₂ := c₂.toLocalConfig)]
  constructor
  · intro h1
    have h2 := c₁.piHat_spec c₂ h
    rwa [h1, map_one] at h2
  · intro h1
    exact c₁.piHat_eq c₂ (by rw [map_one]; exact h1)

theorem zE_mem_Shat : (c₁.zE : c₁.H) ∈ c₁.Shat c₂ :=
  ⟨1, by rw [map_one]; exact (compat_one_iff _).mpr ⟨_, c₁.zE_mem_center, rfl⟩⟩

@[expose] noncomputable def zHat : c₁.Shat c₂ := ⟨c₁.zE, c₁.zE_mem_Shat c₂⟩

theorem piHat_zHat : c₁.piHat c₂ (c₁.zHat c₂) = 1 :=
  (c₁.piHat_eq_one_iff c₂ _).mpr ⟨c₁.zE, c₁.zE_mem_center, rfl⟩

theorem zHat_ne_one : c₁.zHat c₂ ≠ 1 := fun h => by
  have h1 : ((c₁.zHat c₂ : c₁.Shat c₂) : c₁.H) = 1 := by rw [h]; rfl
  exact c₁.zE_ne_one (Subtype.ext h1)

theorem zHat_mem_center : c₁.zHat c₂ ∈ Subgroup.center (c₁.Shat c₂) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  show (g : c₁.H) * c₁.zE = c₁.zE * g
  have h3 := congrArg Subtype.val (c₁.cE_zE (g : c₁.H))
  rw [c₁.cE_val] at h3
  calc (g : c₁.H) * c₁.zE = (g : c₁.H) * c₁.zE * (g : c₁.H)⁻¹ * g := by group
    _ = c₁.zE * g := by rw [h3]

theorem mem_ker_piHat_iff (h : c₁.Shat c₂) : c₁.piHat c₂ h = 1 ↔ h = 1 ∨ h = c₁.zHat c₂ := by
  rw [piHat_eq_one_iff]
  constructor
  · rintro ⟨k, hk, hke⟩
    rcases (c₁.mem_center_iff k).mp hk with rfl | rfl
    · exact Or.inl (Subtype.ext hke)
    · exact Or.inr (Subtype.ext hke)
  · rintro (rfl | rfl)
    · exact ⟨1, Subgroup.one_mem _, rfl⟩
    · exact ⟨_, c₁.zE_mem_center, rfl⟩

theorem center_of_mem_Shat {h : c₁.H} (hS : h ∈ c₁.Shat c₂) (hE : h ∈ c₁.E) :
    ∃ k ∈ Subgroup.center c₁.E, h = k := by
  obtain ⟨s, hs⟩ := hS
  obtain ⟨k, hk, hke⟩ := compat_unique hs (compat_E (c₂ := c₂.toLocalConfig) ⟨h, hE⟩)
  have h1 : c₂.ι s ∈ c₂.ι.range ⊓ c₂.E := by
    refine ⟨⟨s, rfl⟩, ?_⟩
    have e : c₂.ι s = ((c₁.θL c₂.toLocalConfig ⟨h, hE⟩ * k⁻¹ : c₂.E) : c₂.H) := by
      rw [Subgroup.coe_mul, hke, Subgroup.coe_inv]
      group
    rw [e]
    exact SetLike.coe_mem _
  rw [c₂.inf_eq, Subgroup.mem_bot] at h1
  have hs1 : s = 1 := c₂.inj (h1.trans (map_one c₂.ι).symm)
  rw [hs1, map_one] at hs
  exact (compat_one_iff h).mp hs

theorem exists_Shat_mul_E
    (h₁ : c₁.H) : ∃ t ∈ c₁.Shat c₂, ∃ e : c₁.E, h₁ = t * e := by
  obtain ⟨h₂, hh⟩ := exists_compat c₁ c₂.toLocalConfig h₁
  obtain ⟨s, hs⟩ := c₂.ψ_bijective.2 (QuotientGroup.mk h₂ : c₂.H ⧸ c₂.E)
  have hm : (c₂.ι s)⁻¹ * h₂ ∈ c₂.E := QuotientGroup.eq.mp ((c₂.mk_ι s).trans hs)
  set e₂ : c₂.E := ⟨_, hm⟩ with he₂
  set e₁ : c₁.E := c₂.θL c₁ e₂ with he₁
  have hθ : c₁.θL c₂.toLocalConfig e₁ = e₂ := by
    rw [he₁, ← c₁.θL_symm_apply, MulEquiv.apply_symm_apply]
  have hc : c₁.Compat c₂.toLocalConfig (e₁ : c₁.H) (e₂ : c₂.H) := by
    have := compat_E (c₂ := c₂.toLocalConfig) e₁
    rwa [hθ] at this
  refine ⟨h₁ * (e₁ : c₁.H)⁻¹, ⟨s, ?_⟩, e₁, by group⟩
  have h2 := hh.mul hc.inv
  have e : h₂ * ((e₂ : c₂.E) : c₂.H)⁻¹ = c₂.ι s := by
    rw [he₂]
    show h₂ * ((c₂.ι s)⁻¹ * h₂)⁻¹ = c₂.ι s
    group
  rwa [e] at h2

theorem complement_of_split (S' : Subgroup (c₁.Shat c₂)) (hz : c₁.zHat c₂ ∉ S')
    (hsurj : S'.map (c₁.piHat c₂) = ⊤) :
    S'.map (c₁.Shat c₂).subtype ⊓ c₁.E = ⊥ ∧ S'.map (c₁.Shat c₂).subtype ⊔ c₁.E = ⊤ := by
  constructor
  · rw [eq_bot_iff]
    rintro x ⟨⟨t, ht, rfl⟩, hx⟩
    obtain ⟨k, hk, hke⟩ := c₁.center_of_mem_Shat c₂ t.2 hx
    have h1 : c₁.piHat c₂ t = 1 := (c₁.piHat_eq_one_iff c₂ t).mpr ⟨k, hk, hke⟩
    rcases (c₁.mem_ker_piHat_iff c₂ t).mp h1 with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd ht hz
  · rw [eq_top_iff]
    intro h₁ _
    obtain ⟨t, ht, e, rfl⟩ := c₁.exists_Shat_mul_E c₂ h₁
    have hmem : c₁.piHat c₂ ⟨t, ht⟩ ∈ S'.map (c₁.piHat c₂) := hsurj ▸ Subgroup.mem_top _
    obtain ⟨s', hs', hss⟩ := hmem
    have hk : c₁.piHat c₂ (s'⁻¹ * ⟨t, ht⟩) = 1 := by rw [map_mul, map_inv, hss, inv_mul_cancel]
    have hkE : ((s'⁻¹ * ⟨t, ht⟩ : c₁.Shat c₂) : c₁.H) ∈ c₁.E := by
      rcases (c₁.mem_ker_piHat_iff c₂ _).mp hk with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact SetLike.coe_mem _
    have heq : t * (e : c₁.H) =
        (s' : c₁.H) * (((s'⁻¹ * ⟨t, ht⟩ : c₁.Shat c₂) : c₁.H) * e) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨s', hs', rfl⟩)
      (Subgroup.mem_sup_right (Subgroup.mul_mem _ hkE e.2))

end LocalConfig

end CFSG.Sporadic.Co2Smith
