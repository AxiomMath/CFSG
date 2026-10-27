module

public import CFSG.Quasithin.Background.F6CatInstancesG22Shape
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL4Model
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL4G2Uniq

public section

namespace CFSG.Quasithin.F6.GoldAmL4

open CFSG.Quasithin CFSG.Quasithin.F6 CFSG.Quasithin.F6.G22Shape CFSG.Quasithin.F6.G22Perm
  CFSG.Sporadic.Bridge CFSG.Open CFSG.QuasithinUnique

section Map

variable {D E : Type*} [Group D] [Group E] (f : D →* E)

theorem TRel.map {a b s : D} (h : TRel a b s) : TRel (f a) (f b) (f s) where
  ha := by rw [← map_pow, h.ha, map_one]
  hb := by rw [← map_pow, h.hb, map_one]
  hs := by rw [← map_pow, h.hs, map_one]
  hab := by rw [← map_mul, ← map_mul, h.hab]
  hsa := by rw [← map_mul, ← map_mul, h.hsa]
  hsb := by rw [← map_mul, ← map_mul, h.hsb]

theorem ARel.map {a b s x : D} (h : ARel a b s x) : ARel (f a) (f b) (f s) (f x) where
  toTRel := h.toTRel.map f
  hx := by rw [← map_pow, h.hx, map_one]
  hxa := by rw [← map_inv, ← map_mul, ← map_mul, h.hxa]
  hxb := by rw [← map_inv, ← map_mul, ← map_mul, h.hxb, map_mul, map_inv, map_inv]
  hxs := by rw [← map_mul, ← map_mul, h.hxs]

theorem BRel.map {a b s y : D} (h : BRel a b s y) : BRel (f a) (f b) (f s) (f y) where
  toTRel := h.toTRel'.map f
  hy := by rw [← map_pow, h.hy, map_one]
  hyc := by rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, h.hyc, map_mul]
  hyp := by rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, h.hyp]
  hyq := by rw [← map_inv, ← map_mul, ← map_mul, h.hyq, map_mul, map_mul, map_inv]
  hyt := by rw [← map_mul, ← map_mul, ← map_mul, h.hyt, map_mul]

end Map

section Rho

variable
  {k : Type} [Field k] (h2 : (2 : k) = 0) (hk2 : ∀ c : k, c = 0 ∨ c = 1)

@[expose] noncomputable def rhoM : G2Group k :=
  g2HomC h2 (u33GenPG 1) * g2HomC h2 (u33GenPG 1) * g2RhoC h2

@[expose] def rhoML : List ℕ := compL (compL (g22gl 1) (g22gl 1)) u33PiTab

include hk2

theorem repL_rhoM : RepL rhoML (psi h2 hk2 (rhoM h2)) :=
  reprN_mul h2 hk2 (reprN_mul h2 hk2 (reprN_gen h2 hk2 1 (by norm_num))
    (reprN_gen h2 hk2 1 (by norm_num))) (reprN_rho h2 hk2)

theorem rhoM_sq : rhoM h2 * rhoM h2 = 1 :=
  eqN h2 hk2 (reprN_mul h2 hk2 (repL_rhoM h2 hk2) (repL_rhoM h2 hk2))
    ((by decide +kernel : compL rhoML rhoML = g22id) ▸ reprN_one h2 hk2)

theorem rhoM_rel_a :
    rhoM h2 * g2HomC h2 (u33GenPG 0) * rhoM h2 = (g2HomC h2 (u33GenPG 0))⁻¹ :=
  eqN h2 hk2 (reprN_mul h2 hk2 (reprN_mul h2 hk2 (repL_rhoM h2 hk2)
      (reprN_gen h2 hk2 0 (by norm_num))) (repL_rhoM h2 hk2))
    ((by decide +kernel : compL (compL rhoML (g22gl 0)) rhoML = g22gil 0) ▸
      reprN_genInv h2 hk2 0 (by norm_num))

theorem rhoM_rel_b :
    rhoM h2 * g2HomC h2 (u33GenPG 1) * rhoM h2 = (g2HomC h2 (u33GenPG 1))⁻¹ :=
  eqN h2 hk2 (reprN_mul h2 hk2 (reprN_mul h2 hk2 (repL_rhoM h2 hk2)
      (reprN_gen h2 hk2 1 (by norm_num))) (repL_rhoM h2 hk2))
    ((by decide +kernel : compL (compL rhoML (g22gl 1)) rhoML = g22gil 1) ▸
      reprN_genInv h2 hk2 1 (by norm_num))

theorem rhoM_rel_s :
    rhoM h2 * g2HomC h2 (u33GenPG 2) * rhoM h2 = g2HomC h2 (u33GenPG 2) :=
  eqN h2 hk2 (reprN_mul h2 hk2 (reprN_mul h2 hk2 (repL_rhoM h2 hk2)
      (reprN_gen h2 hk2 2 (by norm_num))) (repL_rhoM h2 hk2))
    ((by decide +kernel : compL (compL rhoML (g22gl 2)) rhoML = g22gl 2) ▸
      reprN_gen h2 hk2 2 (by norm_num))

theorem rhoM_rel_x :
    rhoM h2 * g2HomC h2 (u33GenPG 3) * rhoM h2 = g2HomC h2 (u33GenPG 3) :=
  eqN h2 hk2 (reprN_mul h2 hk2 (reprN_mul h2 hk2 (repL_rhoM h2 hk2)
      (reprN_gen h2 hk2 3 (by norm_num))) (repL_rhoM h2 hk2))
    ((by decide +kernel : compL (compL rhoML (g22gl 3)) rhoML = g22gl 3) ▸
      reprN_gen h2 hk2 3 (by norm_num))

theorem rhoM_rel_y : rhoM h2 * g2HomC h2 (u33GenPG 4) * rhoM h2 =
    g2HomC h2 (u33GenPG 0) * (g2HomC h2 (u33GenPG 1))⁻¹ * g2HomC h2 (u33GenPG 4) := by
  have hr : RepL (compL (compL (g22gl 0) (g22gil 1)) (g22gl 4))
      (psi h2 hk2 (g2HomC h2 (u33GenPG 0) * (g2HomC h2 (u33GenPG 1))⁻¹ *
        g2HomC h2 (u33GenPG 4))) :=
    reprN_mul h2 hk2 (reprN_mul h2 hk2 (reprN_gen h2 hk2 0 (by norm_num))
        (reprN_genInv h2 hk2 1 (by norm_num))) (reprN_gen h2 hk2 4 (by norm_num))
  have hl : compL (compL rhoML (g22gl 4)) rhoML =
      compL (compL (g22gl 0) (g22gil 1)) (g22gl 4) := by decide +kernel
  have hr' : RepL (compL (compL rhoML (g22gl 4)) rhoML)
      (psi h2 hk2 (g2HomC h2 (u33GenPG 0) * (g2HomC h2 (u33GenPG 1))⁻¹ *
        g2HomC h2 (u33GenPG 4))) := by rw [hl]; exact hr
  exact eqN h2 hk2 (reprN_mul h2 hk2 (reprN_mul h2 hk2 (repL_rhoM h2 hk2)
      (reprN_gen h2 hk2 4 (by norm_num))) (repL_rhoM h2 hk2)) hr'

end Rho

theorem closure_image_union_eq {J N : Type*} [Group J] [Group N] {f : J →* N} {ρ : N}
    {Φ : J ≃* J} (C : IndexTwoCore f ρ Φ) {H₀ : Subgroup J} (hH : ∀ x ∈ H₀, Φ x ∈ H₀)
    {S : Set J} (hS : H₀ = Subgroup.closure S) {t : J} (ht : t ∈ H₀) :
    Subgroup.closure (f '' S ∪ {f t * ρ}) = C.ext H₀ hH := by
  have hmap : H₀.map f ≤ Subgroup.closure (f '' S ∪ {f t * ρ}) := by
    rw [hS, MonoidHom.map_closure]
    exact Subgroup.closure_mono Set.subset_union_left
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro g (⟨h, hh, rfl⟩ | hg)
    · exact C.map_le_ext hH ⟨h, hS ▸ Subgroup.subset_closure hh, rfl⟩
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact Or.inr (by rw [mul_assoc, C.sq, mul_one]; exact ⟨t, ht, rfl⟩)
  · rintro g (hg | hg)
    · exact hmap hg
    · have h1 := hmap hg
      have h2 := hmap ⟨t, ht, rfl⟩
      have h3 : f t * ρ ∈ Subgroup.closure (f '' S ∪ {f t * ρ}) :=
        Subgroup.subset_closure (Or.inr rfl)
      have e : g = g * ρ * (f t)⁻¹ * (f t * ρ) := by
        calc g = g * (ρ * ρ) := by rw [C.sq, mul_one]
          _ = g * ρ * (f t)⁻¹ * (f t * ρ) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)) h3

section Model


theorem isG22_g2Group {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2) :
    IsG22 (G2Group k) :=
  ⟨k, inferInstance, inferInstance, hk,
    ⟨((QuotientGroup.quotientMulEquivOfEq (center_g2Group k hk)).trans
      QuotientGroup.quotientBot).symm⟩⟩

theorem exists_g22_model :
    ∃ (W : Type) (_ : Group W) (_ : Finite W) (a b s x y ρ : W), IsG22 W ∧ ARel a b s x ∧
      BRel a b s y ∧ ARho a b s x ρ ∧ BRho a b s y ρ ∧
      Nat.card ↥(Subgroup.closure ({a, b, s} : Set W)) = 32 ∧
      ρ ∉ Subgroup.closure ({a, b, s, x} : Set W) ∧
      ρ ∉ Subgroup.closure ({a, b, s, y} : Set W) ∧
      IsTwoLocalAmalgam (Subgroup.closure ({a, b, s, y, ρ} : Set W))
        (Subgroup.closure ({a, b, s, x, ρ} : Set W)) ∧
      Subgroup.closure ({a, b, s, y, ρ} : Set W) ⊓ Subgroup.closure ({a, b, s, x, ρ} : Set W) =
        Subgroup.closure ({a, b, s, ρ} : Set W) := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  have hk2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hk : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have : Finite (G2Group (ZMod 2)) := finite_g2Group
  have D := g2IndexTwoData h2 hk2
  have C := D.toIndexTwoCore
  set f := g2HomC h2 with hf
  have hbb : u33GenPG 1 * u33GenPG 1 ∈ u33Data.T :=
    u33Data.T.mul_mem u33Data.b_mem_T u33Data.b_mem_T
  have hbbA : u33GenPG 1 * u33GenPG 1 ∈ u33Data.A := u33Data.T_le_A hbb
  have hbbB : u33GenPG 1 * u33GenPG 1 ∈ u33Data.B := u33Data.T_le_B hbb
  have hρ : rhoM h2 = f (u33GenPG 1 * u33GenPG 1) * g2RhoC h2 := by
    rw [rhoM, map_mul]
  have eT : Subgroup.closure ({f (u33GenPG 0), f (u33GenPG 1), f (u33GenPG 2), rhoM h2} :
      Set (G2Group (ZMod 2))) = (lat h2 hk2).S := by
    have := closure_image_union_eq C u33Phi'_T u33Data_T hbb
    rw [lat_S, ← this, ← hρ]
    congr 1
    ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.image_insert_eq,
      Set.image_singleton, Set.mem_union]
    tauto
  have eA : Subgroup.closure ({f (u33GenPG 0), f (u33GenPG 1), f (u33GenPG 2), f (u33GenPG 3),
      rhoM h2} : Set (G2Group (ZMod 2))) = (lat h2 hk2).P₁ := by
    have := closure_image_union_eq C u33Phi'_A u33Data_A hbbA
    rw [lat_P₁, ← this, ← hρ]
    congr 1
    ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.image_insert_eq,
      Set.image_singleton, Set.mem_union]
    tauto
  have eB : Subgroup.closure ({f (u33GenPG 0), f (u33GenPG 1), f (u33GenPG 2), f (u33GenPG 4),
      rhoM h2} : Set (G2Group (ZMod 2))) = (lat h2 hk2).P₂ := by
    have := closure_image_union_eq C u33Phi'_B u33Data_B hbbB
    rw [lat_P₂, ← this, ← hρ]
    congr 1
    ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.image_insert_eq,
      Set.image_singleton, Set.mem_union]
    tauto
  have hnot : rhoM h2 ∉ f.range := by
    rintro ⟨w, hw⟩
    apply D.rho_not_mem
    refine ⟨(u33GenPG 1 * u33GenPG 1)⁻¹ * w, ?_⟩
    rw [map_mul, map_inv, hw, hρ]
    group
  have hcard : Nat.card ↥(Subgroup.closure ({f (u33GenPG 0), f (u33GenPG 1), f (u33GenPG 2)} :
      Set (G2Group (ZMod 2)))) = 32 := by
    have e : Subgroup.closure ({f (u33GenPG 0), f (u33GenPG 1), f (u33GenPG 2)} :
        Set (G2Group (ZMod 2))) = (Subgroup.closure
          ({u33GenPG 0, u33GenPG 1, u33GenPG 2} : Set U33G)).map f := by
      rw [MonoidHom.map_closure]
      congr 1
      ext g
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.image_insert_eq,
        Set.image_singleton]
    rw [e, ← Nat.card_congr (Subgroup.equivMapOfInjective _ f D.inj).toEquiv]
    exact u33_card_T'
  have hTL : IsTwoLocalAmalgam (lat h2 hk2).P₂ (lat h2 hk2).P₁ := by
    refine ⟨(lat h2 hk2).isMaximalTwoLocal_P₂, (lat h2 hk2).isMaximalTwoLocal_P₁,
      fun h => (lat h2 hk2).P₂_not_le_P₁ h.le,
      ⟨(lat h2 hk2).sylow.1.toSylow (lat h2 hk2).sylow.2, ?_⟩⟩
    show (lat h2 hk2).S = (lat h2 hk2).P₂ ⊓ (lat h2 hk2).P₁
    rw [inf_comm, lattice_inf_eq]
  refine ⟨G2Group (ZMod 2), inferInstance, inferInstance, f (u33GenPG 0), f (u33GenPG 1),
    f (u33GenPG 2), f (u33GenPG 3), f (u33GenPG 4), rhoM h2, isG22_g2Group hk,
    ARel.map f u33_aRel, BRel.map f u33_bRel,
    ⟨⟨rhoM_sq h2 hk2, rhoM_rel_a h2 hk2, rhoM_rel_b h2 hk2, rhoM_rel_s h2 hk2⟩,
      rhoM_rel_x h2 hk2⟩,
    ⟨⟨rhoM_sq h2 hk2, rhoM_rel_a h2 hk2, rhoM_rel_b h2 hk2, rhoM_rel_s h2 hk2⟩,
      rhoM_rel_y h2 hk2⟩, hcard, ?_, ?_, ?_, ?_⟩
  · intro hmem
    apply hnot
    have : Subgroup.closure ({f (u33GenPG 0), f (u33GenPG 1), f (u33GenPG 2), f (u33GenPG 3)} :
        Set (G2Group (ZMod 2))) ≤ f.range := by
      rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
    exact this hmem
  · intro hmem
    apply hnot
    have : Subgroup.closure ({f (u33GenPG 0), f (u33GenPG 1), f (u33GenPG 2), f (u33GenPG 4)} :
        Set (G2Group (ZMod 2))) ≤ f.range := by
      rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
    exact this hmem
  · rw [eB, eA]
    exact hTL
  · rw [eB, eA, eT, inf_comm, lattice_inf_eq]

end Model

end CFSG.Quasithin.F6.GoldAmL4
