module

public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin.H13

namespace End1222

open CFSG.Quasithin

variable {W : Type*} [CommGroup W]

@[expose] def moveHom (c : MulAut W) : W →* W where
  toFun v := c v * v⁻¹
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, mul_inv_rev]
    rw [mul_comm (b⁻¹) (a⁻¹), mul_mul_mul_comm]

theorem moveHom_apply (c : MulAut W) (v : W) : moveHom c v = c v * v⁻¹ := rfl

section Commuting

variable {Γ : Subgroup (MulAut W)} {c : MulAut W}

theorem comm_apply (hc : ∀ g ∈ Γ, c * g = g * c) {g : MulAut W} (hg : g ∈ Γ) (v : W) :
    c (g v) = g (c v) :=
  congrArg (fun φ : MulAut W => φ v) (hc g hg)

theorem apply_mem_fixV_iff (hc : ∀ g ∈ Γ, c * g = g * c) {v : W} :
    c v ∈ fixV Γ ↔ v ∈ fixV Γ := by
  constructor
  · intro h g hg
    apply c.injective
    rw [comm_apply hc hg]
    exact h g hg
  · intro h g hg
    rw [← comm_apply hc hg, h g hg]

theorem moveHom_apply_smul (hc : ∀ g ∈ Γ, c * g = g * c) {g : MulAut W} (hg : g ∈ Γ) {v : W}
    (hv : moveHom c v ∈ fixV Γ) : moveHom c (g v) = moveHom c v := by
  have hv' : g (c v * v⁻¹) = c v * v⁻¹ := hv g hg
  calc moveHom c (g v) = c (g v) * (g v)⁻¹ := rfl
    _ = g (c v) * (g v)⁻¹ := by rw [comm_apply hc hg]
    _ = g (c v * v⁻¹) := by rw [map_mul, map_inv]
    _ = moveHom c v := hv'

theorem eq_one_of_forall (hcomm : commV Γ = ⊤) (hc : ∀ g ∈ Γ, c * g = g * c)
    (h : ∀ v : W, c v * v⁻¹ ∈ fixV Γ) : c = 1 := by
  have hle : commV Γ ≤ (moveHom c).ker := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨g, hg, v, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv,
      moveHom_apply_smul hc hg (h v), mul_inv_cancel]
  rw [hcomm] at hle
  ext v
  have h1 := MonoidHom.mem_ker.1 (hle (Subgroup.mem_top v))
  rw [moveHom_apply, mul_inv_eq_one] at h1
  exact h1

theorem eq_one_of_exists (hcomm : commV Γ = ⊤)
    (hirr : ∀ J : Subgroup W, fixV Γ ≤ J → (∀ g ∈ Γ, ∀ w ∈ J, g w ∈ J) →
      J = fixV Γ ∨ J = ⊤)
    (hc : ∀ g ∈ Γ, c * g = g * c) (h : ∃ v : W, v ∉ fixV Γ ∧ c v * v⁻¹ ∈ fixV Γ) : c = 1 := by
  obtain ⟨v₀, hv₀, hv₀c⟩ := h
  set J : Subgroup W := (fixV Γ).comap (moveHom c) with hJ
  have hfix : fixV Γ ≤ J := fun v hv => by
    rw [hJ, Subgroup.mem_comap, moveHom_apply]
    exact (fixV Γ).mul_mem ((apply_mem_fixV_iff hc).2 hv) ((fixV Γ).inv_mem hv)
  have hinv : ∀ g ∈ Γ, ∀ w ∈ J, g w ∈ J := fun g hg w hw => by
    rw [hJ, Subgroup.mem_comap] at hw ⊢
    rw [moveHom_apply_smul hc hg hw]
    exact hw
  rcases hirr J hfix hinv with h | h
  · exfalso
    have : v₀ ∈ J := by
      rw [hJ, Subgroup.mem_comap, moveHom_apply]
      exact hv₀c
    rw [h] at this
    exact hv₀ this
  · apply eq_one_of_forall hcomm hc
    intro v
    have : v ∈ J := by rw [h]; trivial
    exact this

theorem fixV_eq_bot_of_irr (hcomm : commV Γ = ⊤)
    (hirr : ∀ J : Subgroup W, (∀ g ∈ Γ, ∀ w ∈ J, g w ∈ J) → J = ⊥ ∨ J = ⊤)
    (hnt : ∃ w : W, w ≠ 1) : fixV Γ = ⊥ := by
  rcases hirr (fixV Γ) (fun g hg w hw => by rw [hw g hg]; exact hw) with h | h
  · exact h
  · exfalso
    have hle : commV Γ ≤ ⊥ := by
      rw [commV, Subgroup.closure_le]
      rintro _ ⟨g, hg, v, rfl⟩
      have hv : v ∈ fixV Γ := by rw [h]; trivial
      rw [SetLike.mem_coe, Subgroup.mem_bot, hv g hg, mul_inv_cancel]
    rw [hcomm] at hle
    obtain ⟨w, hw⟩ := hnt
    exact hw (Subgroup.mem_bot.1 (hle (Subgroup.mem_top w)))

end Commuting

section Model

theorem mk_eq_mk_iff {D : FFModel} (a b : ↥D.sec) :
    (QuotientGroup.mk a : ↥D.sec ⧸ D.ker.subgroupOf D.sec) = QuotientGroup.mk b ↔
      (b : D.Amb) * (a : D.Amb)⁻¹ ∈ D.ker := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [mul_comm]

variable {D : FFModel} {H : Subgroup (MulAut W)} {Z : Subgroup W} {π : D.Gam →* ↥H}

theorem exists_move_of_realizesVia (hR : D.RealizesVia H ⊤ Z π) (hZ : fixV H = Z)
    {c : MulAut W} (hc : ∀ g ∈ H, c * g = g * c) (S : Set D.Gam) {m₀ : D.Amb}
    (hm₀ : m₀ ∈ D.sec) (hm₀k : m₀ ∉ D.ker)
    (h1 : ∀ γ ∈ S, D.act γ m₀ = m₀)
    (h2 : ∀ m ∈ D.sec, (∀ γ ∈ S, D.act γ m * m⁻¹ ∈ D.ker) → m ∈ D.ker ∨ m * m₀⁻¹ ∈ D.ker) :
    ∃ v : W, v ∉ Z ∧ c v * v⁻¹ ∈ Z := by
  obtain ⟨-, -, -, -, -, hsec, -, β, hβs, hβk, hβe⟩ := hR
  let β' : W →* ↥D.sec ⧸ D.ker.subgroupOf D.sec :=
    { toFun := fun w => β ⟨w, trivial⟩
      map_one' := β.map_one
      map_mul' := fun a b => β.map_mul ⟨a, trivial⟩ ⟨b, trivial⟩ }
  have hβ'k : ∀ w : W, β' w = 1 ↔ w ∈ Z := fun w => hβk ⟨w, trivial⟩
  have hcZ : ∀ w : W, c w ∈ Z ↔ w ∈ Z := fun w => by
    rw [← hZ]
    exact apply_mem_fixV_iff hc
  obtain ⟨u₀, hu₀⟩ := hβs (QuotientGroup.mk ⟨m₀, hm₀⟩)
  have hu₀' : β' u₀.1 = QuotientGroup.mk ⟨m₀, hm₀⟩ := hu₀
  have hu₀Z : u₀.1 ∉ Z := by
    intro h
    have h1 := (hβ'k _).2 h
    rw [hu₀'] at h1
    exact hm₀k (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1))
  have hS0 : ∀ γ ∈ S, ((π γ : ↥H) : MulAut W) u₀.1 * u₀.1⁻¹ ∈ Z := by
    intro γ hγ
    have h3 := hβe γ u₀ ⟨m₀, hm₀⟩ trivial (hsec γ m₀ hm₀) hu₀
    have h4 : (⟨D.act γ m₀, hsec γ m₀ hm₀⟩ : ↥D.sec) = ⟨m₀, hm₀⟩ := Subtype.ext (h1 γ hγ)
    rw [← hβ'k, map_mul, map_inv]
    have h5 : β' (((π γ : ↥H) : MulAut W) u₀.1) = β' u₀.1 := by
      change β ⟨_, trivial⟩ = _
      rw [h3, h4, hu₀']
    rw [h5, mul_inv_cancel]
  obtain ⟨m₁, hm₁⟩ := QuotientGroup.mk_surjective (β' (c u₀.1))
  have hS1 : ∀ γ ∈ S, D.act γ (m₁ : D.Amb) * (m₁ : D.Amb)⁻¹ ∈ D.ker := by
    intro γ hγ
    have h3 := hβe γ ⟨c u₀.1, trivial⟩ m₁ trivial (hsec γ m₁ m₁.2) hm₁.symm
    have hmem : ((π γ : ↥H) : MulAut W) ∈ H := (π γ).2
    have h6 : ((π γ : ↥H) : MulAut W) (c u₀.1) =
        c (((π γ : ↥H) : MulAut W) u₀.1 * u₀.1⁻¹) * c u₀.1 := by
      rw [← map_mul, inv_mul_cancel_right]
      exact (comm_apply hc hmem u₀.1).symm
    have h7 : β' (((π γ : ↥H) : MulAut W) (c u₀.1)) = β' (c u₀.1) := by
      rw [h6, map_mul, (hβ'k _).2 ((hcZ _).2 (hS0 γ hγ)), one_mul]
    have h8 : (QuotientGroup.mk ⟨D.act γ (m₁ : D.Amb), hsec γ m₁ m₁.2⟩ :
        ↥D.sec ⧸ D.ker.subgroupOf D.sec) = QuotientGroup.mk m₁ := by
      rw [← h3]
      exact h7.trans hm₁.symm
    exact (mk_eq_mk_iff m₁ _).1 h8.symm
  rcases h2 (m₁ : D.Amb) m₁.2 hS1 with hk | hk
  · exfalso
    have h9 : β' (c u₀.1) = 1 := by
      rw [← hm₁]
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hk)
    exact hu₀Z ((hcZ _).1 ((hβ'k _).1 h9))
  · refine ⟨u₀.1, hu₀Z, ?_⟩
    have h9 : (QuotientGroup.mk ⟨m₀, hm₀⟩ : ↥D.sec ⧸ D.ker.subgroupOf D.sec) =
        QuotientGroup.mk m₁ := (mk_eq_mk_iff _ _).2 hk
    have h10 : β' (c u₀.1) = β' u₀.1 := by rw [← hm₁, ← h9, hu₀']
    exact (hβ'k _).1 (by rw [map_mul, map_inv, h10, mul_inv_cancel])

end Model

end End1222

end CFSG.Quasithin.H13
