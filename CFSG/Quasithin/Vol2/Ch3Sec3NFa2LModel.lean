module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2E5aL
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LVMod

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.CosetGeom CFSG.ASVolI.ChF
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative commutatorElement
open E5aL

theorem exists_odd_lift {A B : Type*} [Group A] [Finite A] [Group B] (f : A →* B) (l : A) (g : B)
    (hg : g ^ 3 = 1) (hl : f l = g) :
    ∃ y : A, y ∈ Subgroup.zpowers l ∧ Odd (orderOf y) ∧ f y = g := by
  have hn : orderOf l ≠ 0 := (orderOf_pos l).ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have h2k : 2 ^ k ≠ 0 := pow_ne_zero k two_ne_zero
  have hdvd : 2 ^ k ∣ orderOf l := ⟨m, hkm⟩
  have hord : orderOf (l ^ 2 ^ k) = m := by
    rw [orderOf_pow_of_dvd h2k hdvd, hkm, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero h2k)]
  have hmod : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
    have h3 : ¬ (3 ∣ 2 ^ k) := fun h => by
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
    omega
  have hf : f (l ^ 2 ^ k) = g ^ (2 ^ k % 3) := by
    rw [map_pow, hl]
    conv_lhs => rw [← Nat.div_add_mod (2 ^ k) 3, pow_add, pow_mul, hg, one_pow, one_mul]
  rcases hmod with h1 | h2
  · refine ⟨l ^ 2 ^ k, Subgroup.pow_mem _ (Subgroup.mem_zpowers l) _, by rw [hord]; exact hm, ?_⟩
    rw [hf, h1, pow_one]
  · refine ⟨(l ^ 2 ^ k)⁻¹, Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers l) _),
      by rw [orderOf_inv, hord]; exact hm, ?_⟩
    rw [map_inv, hf, h2]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ]; exact hg)

@[expose] noncomputable def wcHom :
    Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2)) →* Multiplicative (Fin 6 → ZMod 2) :=
  AddMonoidHom.toMultiplicative (B5FinWedge.wedgeCoord4 (K := ZMod 2)).toAddMonoidHom

theorem toAdd_wcHom (a : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))) :
    Multiplicative.toAdd (wcHom a) = e5wc a := rfl

theorem wcHom_injective : Function.Injective wcHom := by
  intro a b h
  exact e5_eq_of_wc (by simpa [toAdd_wcHom] using congrArg Multiplicative.toAdd h)

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G} {q : ℕ}

theorem A2Cfg.exists_vmod (h36 : A36ForSQTK) (h5 : Stmt3_3_5)
    (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) (hGA : GriessAllModelsStatement) (h128 : Lemma128Two)
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (c : A2Cfg G T M L D H K q) :
    ∃ m : VMod (a2V L T) L (a2Z T), ∃ y₀ ∈ oTwoUpper H, ∃ hy : y₀ ∈ L, m.α ⟨y₀, hy⟩ = gA := by
  obtain ⟨hTL, ⟨e⟩, hc, hmodE, -, -⟩ := c.site
  obtain ⟨-, hLV, -, -, -, -, -⟩ := L3321.setting_facts c.nf.hyp c.TL
  obtain ⟨α, ρ, Z₀, Dm, hαs, hαk, -, hCZ, hαv, hZ₀⟩ :=
    L3321.exists_alpha_model h9 hGA c.nf.hyp c.mPlus_eq hTL e hmodE
  have hVeq : vPlus L T = ⁅vPlus L T, L⁆ := by
    have hbot : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (mPlus L T : Set G) = ⊥ :=
      c.nf.inf_centralizer_mPlus_eq_bot h36 h5 h128 h37 h38 h39
    have h1 := (h7 G T M L D c.nf.hyp).2.2.2.2
    rw [hbot, sup_bot_eq, c.mPlus_eq] at h1
    exact h1
  have hWV : ⁅vPlus L T, L⁆ ≤ vPlus L T := commutator_le_left_of_le_normalizer' hLV
  have hmemC : ∀ y : ↥(vPlus L T), y ∈ commV (autOn L (vPlus L T)) := fun y => by
    exact e5_mem_commV hLV (x := (y : G)) (hVeq.le y.2)
  have hZ0 : ∀ u ∈ Z₀, (u : G) = 1 := by
    intro u hu
    have hzf : u ∈ fixV (autOn L (vPlus L T)) := (Subgroup.mem_inf.1 (hZ₀ hu)).1
    have hzC : (u : G) ∈ Subgroup.centralizer (L : Set G) :=
      (AutOn.mem_fixV_autOn_iff hLV u).1 hzf
    have h2 : (u : G) ∈ vPlus L T ⊓ Subgroup.centralizer (L : Set G) :=
      Subgroup.mem_inf.2 ⟨u.2, hzC⟩
    rw [c.inf_centralizer_L_eq_bot h36 h5 h128 h37 h38 h39, Subgroup.mem_bot] at h2
    exact h2
  let β₀ : ↥(vPlus L T) →* Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2)) :=
    Dm.β.comp
      { toFun := fun y => ⟨y, hmemC y⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
  have hβ₀ : ∀ y, β₀ y = Dm.β ⟨y, hmemC y⟩ := fun y => rfl
  have hinj : Function.Injective β₀ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hu : x ∈ Z₀ := Dm.ker ⟨x, hmemC x⟩ hx
    exact Subtype.ext (hZ0 _ hu)
  have hequiv : ∀ (l : ↥L) (y y' : ↥(vPlus L T)), (y' : G) = (l : G) * (y : G) * (l : G)⁻¹ →
      β₀ y' = FLc.actW (α l) (β₀ y) := by
    intro l y y' hy'
    have hu : ρ (α l) y ∈ commV (autOn L (vPlus L T)) := Dm.inv (α l) _ (hmemC y)
    have key : ρ (α l) y = y' := by
      apply Subtype.ext
      rw [hαv l, FLc.conjAct_coe]
      exact hy'.symm
    have h1 := Dm.equiv (α l) ⟨y, hmemC y⟩ hu
    have h2 : Dm.β ⟨y', hmemC y'⟩ = Dm.β ⟨ρ (α l) y, hu⟩ :=
      congrArg Dm.β (Subtype.ext key.symm)
    rw [hβ₀, hβ₀]
    exact h2.trans h1
  obtain ⟨⟨z₀, hz₀⟩, hz₀ne⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.1 (c.inf_commutator_ne h36 h5 h128 h37 h38 h39)
  have hz₀Z : z₀ ∈ quasithinOmegaOneCenter T := (Subgroup.mem_inf.1 hz₀).1
  have hz₀V : z₀ ∈ vPlus L T := hWV (Subgroup.mem_inf.1 hz₀).2
  have hz₀1 : z₀ ≠ 1 := fun h => hz₀ne (Subtype.ext h)
  have hz₁ne : β₀ ⟨z₀, hz₀V⟩ ≠ 1 := fun h =>
    hz₀1 (congrArg Subtype.val (hinj (h.trans (map_one _).symm)))
  have hPfix : ∀ g ∈ L3321.P2, FLc.actW g (β₀ ⟨z₀, hz₀V⟩) = β₀ ⟨z₀, hz₀V⟩ := by
    intro g hg
    obtain ⟨l, rfl⟩ := hαs g
    have hlC : (l : G) ∈ L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
      rw [hCZ]
      exact Subgroup.mem_map.2 ⟨l, hg, rfl⟩
    have hcent : z₀ * (l : G) = (l : G) * z₀ :=
      Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hlC).2 z₀ hz₀Z
    have hconj : (l : G) * z₀ * (l : G)⁻¹ = z₀ := by
      rw [← hcent, mul_inv_cancel_right]
    exact (hequiv l ⟨z₀, hz₀V⟩ ⟨z₀, hz₀V⟩ hconj.symm).symm
  have hz₁Phi : e5wc (β₀ ⟨z₀, hz₀V⟩) = Pi.single 0 1 := by
    rcases wedge_P2_fixed_actW _ hPfix with h | h
    · exact absurd (toAdd_eq_zero.1 h) hz₁ne
    · show B5FinWedge.wedgeCoord4 (Multiplicative.toAdd (β₀ ⟨z₀, hz₀V⟩)) = _
      rw [h, B5FinWedge.wedgeCoord4_basis]
  have hCZ' : ∀ l : ↥L, α l ∈ L3321.P2 →
      (l : G) ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    intro l hl
    have hlC : (l : G) ∈ L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
      rw [hCZ]
      exact Subgroup.mem_map.2 ⟨l, hl, rfl⟩
    exact (Subgroup.mem_inf.1 hlC).2
  refine ⟨⟨α, wcHom.comp β₀, wcHom_injective.comp hinj, hαs, hLV, ?_, z₀, hz₀Z, hz₀V, hz₁Phi,
    hCZ'⟩, ?_⟩
  ·
    intro l y y' hy'
    show e5wc (β₀ y') = _
    rw [hequiv l y y' hy']
    show B5FinWedge.wedgeCoord4 (Multiplicative.toAdd (FLc.actW (α l) (β₀ y))) = _
    rw [FLc.coord4_actW]
    rfl
  ·
    obtain ⟨l, hl⟩ := hαs gA
    have hlCZ : (l : G) ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
      hCZ' l (by rw [hl]; exact gA_mem_P2)
    have hlH : (l : G) ∈ H := by
      rw [c.hH]
      exact Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨l.2, hlCZ⟩)
    obtain ⟨y, hyl, hyodd, hy⟩ := exists_odd_lift α l gA gA_pow_three hl
    have hyH : (y : G) ∈ H := by
      have : (y : G) ∈ Subgroup.zpowers (l : G) := by
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hyl
        exact Subgroup.mem_zpowers_iff.2 ⟨n, by rw [← hn]; simp⟩
      exact (Subgroup.zpowers_le.2 hlH) this
    refine ⟨(y : G), ?_, y.2, ?_⟩
    · refine Subgroup.subset_closure ⟨hyH, ?_⟩
      rw [Subgroup.orderOf_coe]
      exact hyodd
    · exact hy

end CFSG.Quasithin.H13.NFa2
