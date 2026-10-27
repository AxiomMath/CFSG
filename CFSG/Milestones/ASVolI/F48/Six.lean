module

public import CFSG.Milestones.ASVolI.F48.L3

public section

namespace CFSG.ASVolI

open CFSG.Open

theorem burnsideF48_exists_walk_four {V : Type*} (Γ : SimpleGraph V) {u v : V}
    (h : Γ.dist u v = 4) :
    ∃ z₁ z₂ z₃, Γ.Adj u z₁ ∧ Γ.Adj z₁ z₂ ∧ Γ.Adj z₂ z₃ ∧ Γ.Adj z₃ v := by
  have hr : Γ.Reachable u v := by
    by_contra h'
    rw [SimpleGraph.dist_eq_zero_of_not_reachable h'] at h
    omega
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  rw [h] at hp
  rcases p with _ | ⟨h1, p'⟩
  · simp at hp
  · rename_i z₁
    rcases p' with _ | ⟨h2, p''⟩
    · simp at hp
    · rename_i z₂
      rcases p'' with _ | ⟨h3, p'''⟩
      · simp at hp
      · rename_i z₃
        rcases p''' with _ | ⟨h4, p''''⟩
        · simp at hp
        · rcases p'''' with _ | ⟨_, _⟩
          · exact ⟨z₁, z₂, z₃, h1, h2, h3, h4⟩
          · simp at hp

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_dist_xv_xv_eq_six {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) (hpoly : IsGenPolygon c.graph 6) (a b : c.G0)
    (hab : ¬ ∃ k ∈ stv c c.xv, ∃ l ∈ stv c c.lv, ∃ k' ∈ stv c c.xv, ∃ l' ∈ stv c c.lv,
      ∃ k'' ∈ stv c c.xv, a⁻¹ * b = k * l * k' * l' * k'') :
    c.graph.dist (a • c.xv) (b • c.xv) = 6 := by
  have hle := hpoly.diam_le (a • c.xv) (b • c.xv)
  have hx : CosetGeom.vtype c.xv = false := rfl
  have heven : Even (c.graph.dist (a • c.xv) (b • c.xv)) := by
    rw [burnsideF48_dist_even_iff c.graph CosetGeom.vtype
      (fun _ _ h => CosetGeom.vtype_ne_of_adj h) hpoly.connected, CosetGeom.vtype_smul,
      CosetGeom.vtype_smul]
  have hne0 : c.graph.dist (a • c.xv) (b • c.xv) ≠ 0 := by
    intro h0
    have := (hpoly.connected.dist_eq_zero_iff).1 h0
    refine hab ⟨a⁻¹ * b, ?_, 1, Subgroup.one_mem _, 1, Subgroup.one_mem _, 1, Subgroup.one_mem _,
      1, Subgroup.one_mem _, by group⟩
    rw [MulAction.mem_stabilizer_iff, mul_smul, ← this, inv_smul_smul]
  have hne2 : c.graph.dist (a • c.xv) (b • c.xv) ≠ 2 := by
    intro h2
    obtain ⟨z, h1, h2'⟩ := burnsideF48_exists_mid c.graph h2
    have hz : CosetGeom.vtype z = true := by
      have := CosetGeom.vtype_ne_of_adj h1
      rw [CosetGeom.vtype_smul, hx] at this
      revert this
      cases hzt : CosetGeom.vtype z <;> simp
    obtain ⟨g, rfl⟩ := CosetGeom.exists_smul_eq_γ₁ hz
    obtain ⟨k₁, hk₁, l₁, hl₁, e₁⟩ := (burnsideF48_adj_xv_lv_iff c a g).1 h1
    obtain ⟨k₂, hk₂, l₂, hl₂, e₂⟩ := (burnsideF48_adj_xv_lv_iff c b g).1 h2'.symm
    refine hab ⟨k₁, hk₁, l₁ * l₂⁻¹, (stv c c.lv).mul_mem hl₁ ((stv c c.lv).inv_mem hl₂), k₂⁻¹,
      (stv c c.xv).inv_mem hk₂, 1, Subgroup.one_mem _, 1, Subgroup.one_mem _, ?_⟩
    calc a⁻¹ * b = (a⁻¹ * g) * (b⁻¹ * g)⁻¹ := by group
      _ = k₁ * l₁ * (k₂ * l₂)⁻¹ := by rw [e₁, e₂]
      _ = k₁ * (l₁ * l₂⁻¹) * k₂⁻¹ * 1 * 1 := by group
  have hne4 : c.graph.dist (a • c.xv) (b • c.xv) ≠ 4 := by
    intro h4
    obtain ⟨z₁, z₂, z₃, h1, h2, h3, h4'⟩ := burnsideF48_exists_walk_four c.graph h4
    have hz₁ : CosetGeom.vtype z₁ = true := by
      have := CosetGeom.vtype_ne_of_adj h1
      rw [CosetGeom.vtype_smul, hx] at this
      revert this
      cases hzt : CosetGeom.vtype z₁ <;> simp
    have hz₂ : CosetGeom.vtype z₂ = false := by
      have := CosetGeom.vtype_ne_of_adj h2
      rw [hz₁] at this
      revert this
      cases hzt : CosetGeom.vtype z₂ <;> simp
    have hz₃ : CosetGeom.vtype z₃ = true := by
      have := CosetGeom.vtype_ne_of_adj h3
      rw [hz₂] at this
      revert this
      cases hzt : CosetGeom.vtype z₃ <;> simp
    obtain ⟨g₁, rfl⟩ := CosetGeom.exists_smul_eq_γ₁ hz₁
    obtain ⟨g₂, rfl⟩ := CosetGeom.exists_smul_eq_γ₀ hz₂
    obtain ⟨g₃, rfl⟩ := CosetGeom.exists_smul_eq_γ₁ hz₃
    obtain ⟨k₁, hk₁, l₁, hl₁, e₁⟩ := (burnsideF48_adj_xv_lv_iff c a g₁).1 h1
    obtain ⟨k₂, hk₂, l₂, hl₂, e₂⟩ := (burnsideF48_adj_xv_lv_iff c g₂ g₁).1 h2.symm
    obtain ⟨k₃, hk₃, l₃, hl₃, e₃⟩ := (burnsideF48_adj_xv_lv_iff c g₂ g₃).1 h3
    obtain ⟨k₄, hk₄, l₄, hl₄, e₄⟩ := (burnsideF48_adj_xv_lv_iff c b g₃).1 h4'.symm
    refine hab ⟨k₁, hk₁, l₁ * l₂⁻¹, (stv c c.lv).mul_mem hl₁ ((stv c c.lv).inv_mem hl₂),
      k₂⁻¹ * k₃, (stv c c.xv).mul_mem ((stv c c.xv).inv_mem hk₂) hk₃,
      l₃ * l₄⁻¹, (stv c c.lv).mul_mem hl₃ ((stv c c.lv).inv_mem hl₄), k₄⁻¹,
      (stv c c.xv).inv_mem hk₄, ?_⟩
    calc a⁻¹ * b = (a⁻¹ * g₁) * (g₂⁻¹ * g₁)⁻¹ * (g₂⁻¹ * g₃) * (b⁻¹ * g₃)⁻¹ := by group
      _ = k₁ * l₁ * (k₂ * l₂)⁻¹ * (k₃ * l₃) * (k₄ * l₄)⁻¹ := by rw [e₁, e₂, e₃, e₄]
      _ = k₁ * (l₁ * l₂⁻¹) * (k₂⁻¹ * k₃) * (l₃ * l₄⁻¹) * k₄⁻¹ := by group
  rw [Nat.even_iff] at heven
  omega

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_cartan_six {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) {E : Type} [Group E] (e : c.G0 ≃* E) (M₁ M₂ : Subgroup E)
    (hx : ∀ x : c.G0, x ∈ stv c c.xv ↔ e x ∈ M₁) (hl : ∀ x : c.G0, x ∈ stv c c.lv ↔ e x ∈ M₂)
    (hpoly : IsGenPolygon c.graph 6) (Q : Subgroup c.G0) (n w h : E) (hn1 : n ∈ M₁)
    (hn2 : n ∉ M₂) (hh1 : h ∈ M₁) (hh2 : h ∈ M₂) (hh3 : n⁻¹ * h * n ∈ M₂)
    (hh4 : w⁻¹ * h * w ∈ M₁)
    (hw : ¬ ∃ k ∈ M₁, ∃ l ∈ M₂, ∃ k' ∈ M₁, ∃ l' ∈ M₂, ∃ k'' ∈ M₁, w = k * l * k' * l' * k'')
    (hQ : ∀ q ∈ Q, e.symm h * q * (e.symm h)⁻¹ = q → q = 1) :
    ∃ b u₁ u₂ : c.Γ, c.graph.dist c.xv b = 6 ∧ c.graph.Adj c.xv u₁ ∧ c.graph.Adj c.xv u₂ ∧
      u₁ ≠ u₂ ∧ ∃ h : c.G0, h • c.xv = c.xv ∧ h • b = b ∧ h • u₁ = u₁ ∧ h • u₂ = u₂ ∧
        ∀ q ∈ Q, h * q * h⁻¹ = q → q = 1 := by
  have hdist : c.graph.dist c.xv (e.symm w • c.xv) = 6 := by
    have := burnsideF48_dist_xv_xv_eq_six c hpoly 1 (e.symm w) (by
      rintro ⟨k, hk, l, hl', k', hk', l', hl'', k'', hk'', hkl⟩
      refine hw ⟨e k, (hx k).1 hk, e l, (hl l).1 hl', e k', (hx k').1 hk', e l', (hl l').1 hl'',
        e k'', (hx k'').1 hk'', ?_⟩
      have := congrArg e hkl
      simpa [map_mul] using this)
    rwa [one_smul] at this
  have hhb : e.symm h • (e.symm w • c.xv) = e.symm w • c.xv := by
    have : (e.symm w)⁻¹ * e.symm h * e.symm w ∈ stv c c.xv := (hx _).2 (by simpa [map_mul, map_inv] using hh4)
    rw [← mul_smul, show e.symm h * e.symm w = e.symm w * ((e.symm w)⁻¹ * e.symm h * e.symm w) by
      group, mul_smul, MulAction.mem_stabilizer_iff.1 this]
  exact burnsideF48_cartan_shape c e M₁ M₂ hx hl 6 Q n h hn1 hn2 hh1 hh2 hh3 _ hdist hhb hQ

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_cartanFPF_six {κ : ChF.GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime)
    (hm : 3 ≤ κ.m) (hκ : κ.m = 6)
    (hpoly : IsGenPolygon (burnsideF48_setting hyp hp hm).ι.graph 6) (n w h : E)
    (hn1 : n ∈ M₁) (hn2 : n ∉ M₂) (hh1 : h ∈ M₁) (hh2 : h ∈ M₂) (hh3 : n⁻¹ * h * n ∈ M₂)
    (hh4 : w⁻¹ * h * w ∈ M₁)
    (hw : ¬ ∃ k ∈ M₁, ∃ l ∈ M₂, ∃ k' ∈ M₁, ∃ l' ∈ M₂, ∃ k'' ∈ M₁, w = k * l * k' * l' * k'')
    (hQ : ∀ q ∈ pCoreOf p (Gp ⊓ M₁), h * q * h⁻¹ = q → q = 1) :
    (burnsideF48_setting hyp hp hm).CartanFPF := by
  obtain ⟨b, u₁, u₂, hb, h1, h2, hne, g, hg⟩ := burnsideF48_cartan_six
    (burnsideF48_setting hyp hp hm).ι (burnsideF48_toEquiv hyp hp hm) M₁ M₂
    (burnsideF48_mem_stv_xv_equiv hyp hp hm) (burnsideF48_mem_stv_lv_equiv hyp hp hm) hpoly _ n w h
    hn1 hn2 hh1 hh2 hh3 hh4 hw (burnsideF48_qbar_centralizer hyp hp hm h hQ)
  exact ⟨b, u₁, u₂, hb.trans hκ.symm, h1, h2, hne, g, hg⟩

theorem burnsideF48_split_five {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M₁ ⊓ M₂, e = n * h) {g : E} (hg : g ∈ Gp)
    (hkl : ∃ k ∈ M₁, ∃ l ∈ M₂, ∃ k' ∈ M₁, ∃ l' ∈ M₂, ∃ k'' ∈ M₁,
      g = k * l * k' * l' * k'') :
    ∃ k ∈ Gp ⊓ M₁, ∃ l ∈ Gp ⊓ M₂, ∃ k' ∈ Gp ⊓ M₁, ∃ l' ∈ Gp ⊓ M₂, ∃ k'' ∈ Gp ⊓ M₁,
      g = k * l * k' * l' * k'' := by
  obtain ⟨k, hk, l, hl, k', hk', l', hl', k'', hk'', rfl⟩ := hkl
  obtain ⟨n₁, hn₁, h₁, hh₁, he₁⟩ := hsplit k
  obtain ⟨n₂, hn₂, h₂, hh₂, he₂⟩ := hsplit k''⁻¹
  obtain ⟨n₃, hn₃, h₃, hh₃, he₃⟩ := hsplit (h₁ * l)
  obtain ⟨n₄, hn₄, h₄, hh₄, he₄⟩ := hsplit (l' * h₂⁻¹)⁻¹
  have h₁₁ : h₁ ∈ M₁ := (Subgroup.mem_inf.1 hh₁).1
  have h₁₂ : h₁ ∈ M₂ := (Subgroup.mem_inf.1 hh₁).2
  have h₂₁ : h₂ ∈ M₁ := (Subgroup.mem_inf.1 hh₂).1
  have h₂₂ : h₂ ∈ M₂ := (Subgroup.mem_inf.1 hh₂).2
  have h₃₁ : h₃ ∈ M₁ := (Subgroup.mem_inf.1 hh₃).1
  have h₃₂ : h₃ ∈ M₂ := (Subgroup.mem_inf.1 hh₃).2
  have h₄₁ : h₄ ∈ M₁ := (Subgroup.mem_inf.1 hh₄).1
  have h₄₂ : h₄ ∈ M₂ := (Subgroup.mem_inf.1 hh₄).2
  have hn₁M : n₁ ∈ M₁ := by
    have : n₁ = k * h₁⁻¹ := by rw [he₁]; group
    rw [this]
    exact M₁.mul_mem hk (M₁.inv_mem h₁₁)
  have hn₂M : n₂⁻¹ ∈ M₁ := by
    have : n₂⁻¹ = h₂ * k'' := by
      have h := congrArg (fun x => x⁻¹) he₂
      simp only [inv_inv, mul_inv_rev] at h
      rw [h]
      group
    rw [this]
    exact M₁.mul_mem h₂₁ hk''
  have hn₃M : n₃ ∈ M₂ := by
    have : n₃ = h₁ * l * h₃⁻¹ := by rw [he₃] at *; group
    rw [this]
    exact M₂.mul_mem (M₂.mul_mem h₁₂ hl) (M₂.inv_mem h₃₂)
  have hn₄M : n₄⁻¹ ∈ M₂ := by
    have : n₄⁻¹ = h₄ * (l' * h₂⁻¹) := by
      have h := congrArg (fun x => x⁻¹) he₄
      simp only [inv_inv, mul_inv_rev] at h
      rw [h]
      group
    rw [this]
    exact M₂.mul_mem h₄₂ (M₂.mul_mem hl' (M₂.inv_mem h₂₂))
  have hk₃ : h₃ * k' * h₄⁻¹ ∈ M₁ :=
    M₁.mul_mem (M₁.mul_mem h₃₁ hk') (M₁.inv_mem h₄₁)
  have hkey : k * l * k' * l' * k'' = n₁ * n₃ * (h₃ * k' * h₄⁻¹) * n₄⁻¹ * n₂⁻¹ := by
    have e₂' : k'' = h₂⁻¹ * n₂⁻¹ := by
      have : k'' = (k''⁻¹)⁻¹ := (inv_inv k'').symm
      rw [this, he₂]
      group
    have e₄' : l' = h₄⁻¹ * n₄⁻¹ * h₂ := by
      have h := congrArg (fun x => x⁻¹) he₄
      simp only [inv_inv, mul_inv_rev] at h
      have : l' * h₂⁻¹ = h₄⁻¹ * n₄⁻¹ := by
        have h' : (l' * h₂⁻¹)⁻¹⁻¹ = (n₄ * h₄)⁻¹ := by rw [← he₄]
        simpa [mul_inv_rev] using h'
      calc l' = (l' * h₂⁻¹) * h₂ := by group
        _ = h₄⁻¹ * n₄⁻¹ * h₂ := by rw [this]
    have e₃' : h₁ * l = n₃ * h₃ := he₃
    calc k * l * k' * l' * k'' = (n₁ * h₁) * l * k' * l' * k'' := by rw [← he₁]
      _ = n₁ * (h₁ * l) * k' * (l' * k'') := by group
      _ = n₁ * (n₃ * h₃) * k' * (h₄⁻¹ * n₄⁻¹ * h₂ * (h₂⁻¹ * n₂⁻¹)) := by rw [← e₃', e₂', e₄']
      _ = n₁ * n₃ * (h₃ * k' * h₄⁻¹) * n₄⁻¹ * n₂⁻¹ := by group
  refine ⟨n₁, Subgroup.mem_inf.2 ⟨hn₁, hn₁M⟩, n₃, Subgroup.mem_inf.2 ⟨hn₃, hn₃M⟩,
    h₃ * k' * h₄⁻¹, Subgroup.mem_inf.2 ⟨?_, hk₃⟩, n₄⁻¹, Subgroup.mem_inf.2 ⟨Gp.inv_mem hn₄, hn₄M⟩,
    n₂⁻¹, Subgroup.mem_inf.2 ⟨Gp.inv_mem hn₂, hn₂M⟩, hkey⟩
  have : h₃ * k' * h₄⁻¹ = n₃⁻¹ * (n₁⁻¹ * (n₁ * n₃ * (h₃ * k' * h₄⁻¹) * n₄⁻¹ * n₂⁻¹) * n₂ * n₄) := by
    group
  rw [this, ← hkey]
  exact Gp.mul_mem (Gp.inv_mem hn₃) (Gp.mul_mem (Gp.mul_mem (Gp.mul_mem (Gp.inv_mem hn₁) hg) hn₂) hn₄)

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion in
theorem burnsideF48_cartanFPF_of_data_six {κ : ChF.GLKind} {p f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : ChF.HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ κ.m)
    (hκ : κ.m = 6) (hpoly : IsGenPolygon (burnsideF48_setting hyp hp hm).ι.graph 6)
    {G' : Type} [Group G'] (ε : G' ≃* ↥Gp) (P₁ P₂ U : Subgroup G')
    (hP₁ : ∀ g : G', ((ε g : ↥Gp) : E) ∈ M₁ ↔ g ∈ P₁)
    (hP₂ : ∀ g : G', ((ε g : ↥Gp) : E) ∈ M₂ ↔ g ∈ P₂)
    (hU : ChF.IsSylowOf p ((U.map ε.toMonoidHom).map Gp.subtype) Gp) (hUP : U ≤ P₁)
    (n w h : G') (hn1 : n ∈ P₁) (hn2 : n ∉ P₂) (hh1 : h ∈ P₁) (hh2 : h ∈ P₂)
    (hh3 : n⁻¹ * h * n ∈ P₂) (hh4 : w⁻¹ * h * w ∈ P₁)
    (hw : ¬ ∃ k ∈ P₁, ∃ l ∈ P₂, ∃ k' ∈ P₁, ∃ l' ∈ P₂, ∃ k'' ∈ P₁, w = k * l * k' * l' * k'')
    (hQ : ∀ q ∈ U, n⁻¹ * q * n ∈ U → h * q * h⁻¹ = q → q = 1) :
    (burnsideF48_setting hyp hp hm).CartanFPF := by
  haveI : Finite E := hyp.finite
  set ι : G' → E := fun g => ((ε g : ↥Gp) : E) with hι
  have hmul : ∀ a b, ι (a * b) = ι a * ι b := fun a b => by simp [hι]
  have hinv : ∀ a, ι a⁻¹ = (ι a)⁻¹ := fun a => by simp [hι]
  have hinj : Function.Injective ι := fun a b hab => ε.injective (Subtype.ext hab)
  have hmemGp : ∀ a, ι a ∈ Gp := fun a => (ε a).2
  have hconj : ∀ a b c : G', ι (a⁻¹ * b * c) = (ι a)⁻¹ * ι b * ι c := fun a b c => by
    rw [hmul, hmul, hinv]
  refine burnsideF48_cartanFPF_six hyp hp hm hκ hpoly (ι n) (ι w) (ι h) ((hP₁ n).2 hn1)
    (fun hc => hn2 ((hP₂ n).1 hc)) ((hP₁ h).2 hh1) ((hP₂ h).2 hh2) ?_ ?_ ?_ ?_
  · rw [← hconj]
    exact (hP₂ _).2 hh3
  · rw [← hconj]
    exact (hP₁ _).2 hh4
  · intro hkl
    obtain ⟨k, hk, l, hl, k', hk', l', hl', k'', hk'', hwkl⟩ :=
      burnsideF48_split_five hyp.split (hmemGp w) hkl
    have ha : ι (ε.symm ⟨k, (Subgroup.mem_inf.1 hk).1⟩) = k := by simp [hι]
    have hb : ι (ε.symm ⟨l, (Subgroup.mem_inf.1 hl).1⟩) = l := by simp [hι]
    have hc : ι (ε.symm ⟨k', (Subgroup.mem_inf.1 hk').1⟩) = k' := by simp [hι]
    have hd : ι (ε.symm ⟨l', (Subgroup.mem_inf.1 hl').1⟩) = l' := by simp [hι]
    have he : ι (ε.symm ⟨k'', (Subgroup.mem_inf.1 hk'').1⟩) = k'' := by simp [hι]
    refine hw ⟨ε.symm ⟨k, (Subgroup.mem_inf.1 hk).1⟩,
      (hP₁ _).1 (by show ι _ ∈ M₁; rw [ha]; exact (Subgroup.mem_inf.1 hk).2),
      ε.symm ⟨l, (Subgroup.mem_inf.1 hl).1⟩,
      (hP₂ _).1 (by show ι _ ∈ M₂; rw [hb]; exact (Subgroup.mem_inf.1 hl).2),
      ε.symm ⟨k', (Subgroup.mem_inf.1 hk').1⟩,
      (hP₁ _).1 (by show ι _ ∈ M₁; rw [hc]; exact (Subgroup.mem_inf.1 hk').2),
      ε.symm ⟨l', (Subgroup.mem_inf.1 hl').1⟩,
      (hP₂ _).1 (by show ι _ ∈ M₂; rw [hd]; exact (Subgroup.mem_inf.1 hl').2),
      ε.symm ⟨k'', (Subgroup.mem_inf.1 hk'').1⟩,
      (hP₁ _).1 (by show ι _ ∈ M₁; rw [he]; exact (Subgroup.mem_inf.1 hk'').2), hinj ?_⟩
    rw [hmul, hmul, hmul, hmul, ha, hb, hc, hd, he, hwkl]
  · intro q hq hcomm
    have hSP : (U.map ε.toMonoidHom).map Gp.subtype ≤ Gp ⊓ M₁ := by
      rintro _ ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      exact Subgroup.mem_inf.2 ⟨(ε u).2, (hP₁ u).2 (hUP hu)⟩
    have hcore := burnsideF48_pCoreOf_le_sylow hp hU hSP (inf_le_left : Gp ⊓ M₁ ≤ Gp)
    have hqGp : q ∈ Gp := (Subgroup.mem_inf.1 (burnsideF48_pCoreOf_le_self p _ hq)).1
    set q₀ : G' := ε.symm ⟨q, hqGp⟩ with hq₀
    have hιq₀ : ι q₀ = q := by simp [hι, hq₀]
    have hq₀U : q₀ ∈ U := by
      have := hcore hq
      rw [← hιq₀] at this
      exact (burnsideF48_mem_map_map ε U q₀).1 this
    have hnM : (ι n)⁻¹ ∈ Gp ⊓ M₁ :=
      (Gp ⊓ M₁).inv_mem (Subgroup.mem_inf.2 ⟨hmemGp n, (hP₁ n).2 hn1⟩)
    have hnqU : n⁻¹ * q₀ * n ∈ U := by
      have h1 : (ι n)⁻¹ * q * ι n ∈ pCoreOf p (Gp ⊓ M₁) := by
        simpa [inv_inv] using burnsideF48_pCoreOf_conj hnM hq
      have h2 := hcore h1
      rw [← hιq₀, ← hconj] at h2
      exact (burnsideF48_mem_map_map ε U _).1 h2
    have hcomm' : h * q₀ * h⁻¹ = q₀ := by
      apply hinj
      rw [hmul, hmul, hinv, hιq₀]
      exact hcomm
    have := hQ q₀ hq₀U hnqU hcomm'
    rw [← hιq₀, this]
    simp [hι]

end CFSG.ASVolI
