module

public import CFSG.RankThree.GF2n.Smith81.OrthE1TripleNu
public import CFSG.RankThree.GF2n.Smith81.OrthE1TripleFrame
public import CFSG.RankThree.GF2n.Smith81.OrthSL2Cube

public section

open scoped Matrix

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

namespace Triple

variable {K : Type} [Field K]

instance instFiniteT3E [Finite K] : Finite (T3E K) :=
  Finite.of_injective (fun g : T3E K => (g : Tensor3 K → Tensor3 K)) DFunLike.coe_injective

section Line

variable [Finite K] [CharP K 2]

@[expose] def lineNil : Module.End K (Tensor3 K) where
  toFun T a b c := if a = 0 then T 1 b c else 0
  map_add' T T' := by
    funext a b c
    by_cases h : a = 0 <;> simp [h]
  map_smul' r T := by
    funext a b c
    by_cases h : a = 0 <;> simp [h]

theorem act0E_unipSL_apply (r : K) (T : Tensor3 K) :
    act0E (unipSL r) T = T + r • lineNil T := by
  funext a b c
  fin_cases a <;> simp [act0E_apply, tensor3Act0, unipSL_apply, lineNil, Fin.sum_univ_two]

theorem conj_unip_eq (γ : T3E K) (a b : K) (hb : b ≠ 0)
    (h : γ * act0E (unipSL b) * γ⁻¹ = act0E (unipSL a)) (d : K) :
    γ * act0E (unipSL d) * γ⁻¹ = act0E (unipSL (d * a / b)) := by
  have key : ∀ T, γ (lineNil (γ.symm T)) = (a / b) • lineNil T := by
    intro T
    have h1 := LinearEquiv.congr_fun h T
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, act0E_unipSL_apply,
      act0E_unipSL_apply] at h1
    change γ (γ.symm T + b • lineNil (γ.symm T)) = T + a • lineNil T at h1
    rw [map_add, map_smul, LinearEquiv.apply_symm_apply] at h1
    have h2 : b • γ (lineNil (γ.symm T)) = a • lineNil T := add_left_cancel h1
    rw [div_eq_inv_mul, mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hb, one_smul]
  apply LinearEquiv.ext
  intro T
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, act0E_unipSL_apply, act0E_unipSL_apply]
  change γ (γ.symm T + d • lineNil (γ.symm T)) = T + (d * a / b) • lineNil T
  rw [map_add, map_smul, LinearEquiv.apply_symm_apply, key, smul_smul]
  congr 2
  ring

theorem lineG_conj_inf_or (γ : T3E K) :
    lineG ⊓ lineG.map (MulAut.conj γ).toMonoidHom = ⊥ ∨
      lineG.map (MulAut.conj γ).toMonoidHom = lineG := by
  by_cases h : lineG ⊓ lineG.map (MulAut.conj γ).toMonoidHom = ⊥
  · exact Or.inl h
  right
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h
  obtain ⟨hxl, y, hy, hxy⟩ := Subgroup.mem_inf.mp x.2
  obtain ⟨a, ha⟩ := mem_lineG_iff.mp hxl
  obtain ⟨b, hb⟩ := mem_lineG_iff.mp hy
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply hx1
    apply Subtype.ext
    have : (y : T3E K) = 1 := by rw [hb, unipSL_zero, map_one]
    have h3 : (x : T3E K) = γ * y * γ⁻¹ := hxy.symm
    rw [h3, this]
    simp
  have hbx : γ * act0E (unipSL b) * γ⁻¹ = act0E (unipSL a) := by
    have h3 : (x : T3E K) = γ * y * γ⁻¹ := hxy.symm
    rw [← hb, ← ha]
    exact h3.symm
  have hle : lineG.map (MulAut.conj γ).toMonoidHom ≤ lineG := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨d, hd⟩ := mem_lineG_iff.mp hz
    rw [mem_lineG_iff]
    refine ⟨d * a / b, ?_⟩
    rw [hd]
    exact conj_unip_eq γ a b hb0 hbx d
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj γ).injective]

end Line

section Facts

theorem notTwoPow_map {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) {y : G} (hy : NotTwoPow y) : NotTwoPow (f y) := by
  intro k h
  apply hy k
  apply hf
  rw [map_pow, h, map_one]

theorem exists_notTwoPow_of_not_pgroup {G : Type*} [Group G] (h : ¬ IsPGroup 2 G) :
    ∃ y : G, NotTwoPow y := by
  by_contra hne
  push Not at hne
  apply h
  intro g
  by_contra hg
  push Not at hg
  exact hne g hg

theorem notTwoPow_of_not_pgroup_sub {G : Type*} [Group G] {H : Subgroup G}
    (h : ¬ IsPGroup 2 ↥H) : ∃ y ∈ H, NotTwoPow y := by
  obtain ⟨y, hy⟩ := exists_notTwoPow_of_not_pgroup h
  refine ⟨y, y.2, fun k hk => hy k ?_⟩
  exact Subtype.ext (by simpa using hk)

variable [Finite K] [CharP K 2]

theorem not_pgroup_SL2 (hK : 4 ≤ Nat.card K) :
    ¬ IsPGroup 2 (Matrix.SpecialLinearGroup (Fin 2) K) := fun h =>
  orth_not_pgroup_statedSL hK
    (h.of_equiv (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K))

theorem not_pgroup_range {G : Type*} [Group G] (f : Matrix.SpecialLinearGroup (Fin 2) K →* G)
    (hf : Function.Injective f) (hK : 4 ≤ Nat.card K) : ¬ IsPGroup 2 ↥f.range := by
  intro h
  apply not_pgroup_SL2 hK
  exact h.of_injective (f.rangeRestrict) (fun a b hab =>
    hf (congrArg Subtype.val hab))

theorem exists_notTwoPow_rowG (hK : 4 ≤ Nat.card K) : ∃ y ∈ (rowG : Subgroup (T3E K)),
    NotTwoPow y :=
  notTwoPow_of_not_pgroup_sub (not_pgroup_range _ act1E_injective hK)

theorem simple_range {G : Type*} [Group G] (f : Matrix.SpecialLinearGroup (Fin 2) K →* G)
    (hf : Function.Injective f) (hK : 4 ≤ Nat.card K) : IsSimpleGroup ↥f.range := by
  haveI := CFSG.CGT.PushingUpLit.A78.isSimpleGroup_SL2_charTwo K hK
  exact (MonoidHom.ofInjective hf).symm.isSimpleGroup

theorem simple_rowG (hK : 4 ≤ Nat.card K) : IsSimpleGroup ↥(rowG (K := K)) :=
  simple_range _ act1E_injective hK

theorem simple_colG (hK : 4 ≤ Nat.card K) : IsSimpleGroup ↥(colG (K := K)) :=
  simple_range _ act2E_injective hK

theorem not_comm_rowG : ¬ IsMulCommutative ↥(rowG (K := K)) :=
  not_comm_of_injective sl2_not_commutative _ act1E_injective

theorem not_comm_colG : ¬ IsMulCommutative ↥(colG (K := K)) :=
  not_comm_of_injective sl2_not_commutative _ act2E_injective

theorem simple_map {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (H : Subgroup G)
    [IsSimpleGroup ↥H] : IsSimpleGroup ↥(H.map e.toMonoidHom) :=
  (Subgroup.equivMapOfInjective H e.toMonoidHom e.injective).symm.isSimpleGroup

theorem not_comm_map {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (H : Subgroup G)
    (hH : ¬ IsMulCommutative ↥H) : ¬ IsMulCommutative ↥(H.map e.toMonoidHom) := by
  intro h
  apply hH
  refine ⟨⟨fun a b => ?_⟩⟩
  have := h.is_comm.comm ⟨e a, a, a.2, rfl⟩ ⟨e b, b, b.2, rfl⟩
  have h2 : e a * e b = e b * e a := congrArg Subtype.val this
  apply Subtype.ext
  apply e.injective
  rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
  exact h2

end Facts

section Cols

variable [Finite K] [CharP K 2]

theorem conjFlip_conjFlip (g : T3E K) : conjFlip (conjFlip g) = g := by
  rw [conjFlip_apply, conjFlip_apply]
  calc (flipE : T3E K) * (flipE * g * flipE) * flipE = (flipE * flipE) * g * (flipE * flipE) := by
        simp only [mul_assoc]
    _ = g := by rw [flipE_mul_self, one_mul, mul_one]

theorem conjFlip_mem_rowG {g : T3E K} (hg : g ∈ (colG : Subgroup (T3E K))) :
    conjFlip g ∈ (rowG : Subgroup (T3E K)) := by
  obtain ⟨A, rfl⟩ := hg
  rw [conjFlip_act2E]
  exact ⟨A, rfl⟩

theorem conjFlip_mem_colG {g : T3E K} (hg : g ∈ (rowG : Subgroup (T3E K))) :
    conjFlip g ∈ (colG : Subgroup (T3E K)) := by
  obtain ⟨A, rfl⟩ := hg
  rw [conjFlip_act1E]
  exact ⟨A, rfl⟩

theorem conjFlip_mem_lineG {g : T3E K} (hg : g ∈ (lineG : Subgroup (T3E K))) :
    conjFlip g ∈ (lineG : Subgroup (T3E K)) := by
  obtain ⟨c, rfl⟩ := mem_lineG_iff.mp hg
  rw [conjFlip_act0E]
  exact mem_lineG_iff.mpr ⟨c, rfl⟩

theorem ct1_cols (hKF11a : Sp4InvolutionStatement) (hK : 4 ≤ Nat.card K)
    (κ : K) (𝒩 : Subgroup (T3E K)) (h𝒩O : 𝒩 ≤ Ok κ) (h4 : 4 ≤ Nat.card 𝒩)
    (hsplit : ∀ n ∈ 𝒩, ∃ u ∈ lineG, ∃ f ∈ colG, n = u * f)
    (hsq : ∀ n ∈ 𝒩, n * n = 1) (hTI : 𝒩 ⊓ lineG = ⊥)
    (y : T3E K) (hyO : y ∈ Ok κ) (hyc : ∀ g ∈ rowG, y * g = g * y)
    (hyn : ∀ n ∈ 𝒩, y * n = n * y) (hy2 : NotTwoPow y) :
    κ = 0 ∧ 𝒩 ≤ colG := by
  have hinj : Function.Injective (conjFlip (K := K)).toMonoidHom := (conjFlip (K := K)).injective
  obtain ⟨hκ, hle⟩ := ct1_rows hKF11a hK κ (𝒩.map (conjFlip (K := K)).toMonoidHom)
    (by
      rintro _ ⟨n, hn, rfl⟩
      exact (conjFlip_mem_Ok κ n).mpr (h𝒩O hn))
    (by rw [Subgroup.card_map_of_injective hinj]; exact h4)
    (by
      rintro _ ⟨n, hn, rfl⟩
      obtain ⟨u, hu, f, hf, rfl⟩ := hsplit n hn
      refine ⟨u, hu, conjFlip f, conjFlip_mem_rowG hf, ?_⟩
      obtain ⟨c, rfl⟩ := mem_lineG_iff.mp hu
      change conjFlip (act0E (unipSL c) * f) = act0E (unipSL c) * conjFlip f
      rw [map_mul, conjFlip_act0E])
    (by
      rintro _ ⟨n, hn, rfl⟩
      change conjFlip n * conjFlip n = 1
      rw [← map_mul, hsq n hn, map_one])
    (by
      rw [Subgroup.eq_bot_iff_forall]
      rintro x ⟨⟨n, hn, rfl⟩, hxl⟩
      have hn' : n ∈ (lineG : Subgroup (T3E K)) := by
        have := conjFlip_mem_lineG hxl
        change conjFlip (conjFlip n) ∈ _ at this
        rwa [conjFlip_conjFlip] at this
      have : n ∈ 𝒩 ⊓ lineG := ⟨hn, hn'⟩
      rw [hTI, Subgroup.mem_bot] at this
      subst this
      exact map_one _)
    (conjFlip y) ((conjFlip_mem_Ok κ y).mpr hyO)
    (by
      intro g hg
      have hg0 := conjFlip_mem_rowG hg
      have h := congrArg conjFlip (hyc _ hg0)
      rw [map_mul, map_mul, conjFlip_conjFlip] at h
      exact h)
    (by
      rintro _ ⟨n, hn, rfl⟩
      change conjFlip y * conjFlip n = conjFlip n * conjFlip y
      rw [← map_mul, ← map_mul, hyn n hn])
    (notTwoPow_map conjFlip.toMonoidHom hinj hy2)
  refine ⟨hκ, fun n hn => ?_⟩
  have h1 : conjFlip n ∈ (rowG : Subgroup (T3E K)) := hle ⟨n, hn, rfl⟩
  have h2 := conjFlip_mem_colG h1
  rwa [conjFlip_conjFlip] at h2

end Cols

section CoreThm

variable [Finite K] [CharP K 2]

abbrev cjH (γ : T3E K) : T3E K →* T3E K := (MulAut.conj γ).toMonoidHom

theorem cjH_apply (γ g : T3E K) : cjH γ g = γ * g * γ⁻¹ := rfl

theorem cjH_injective (γ : T3E K) : Function.Injective (cjH γ) := (MulAut.conj γ).injective

theorem cjH_cjH_inv (γ g : T3E K) : cjH γ (cjH γ⁻¹ g) = g := by
  simp [cjH_apply, mul_assoc]

theorem cjH_inv_cjH (γ g : T3E K) : cjH γ⁻¹ (cjH γ g) = g := by
  simp [cjH_apply, mul_assoc]

theorem lineG_comm_rowG : ∀ u ∈ (lineG : Subgroup (T3E K)), ∀ f ∈ (rowG : Subgroup (T3E K)),
    u * f = f * u := by
  intro u hu f hf
  obtain ⟨a, rfl⟩ := mem_lineG_iff.mp hu
  obtain ⟨B, rfl⟩ := hf
  exact act0E_comm_act1E _ _

theorem lineG_comm_colG : ∀ u ∈ (lineG : Subgroup (T3E K)), ∀ f ∈ (colG : Subgroup (T3E K)),
    u * f = f * u := by
  intro u hu f hf
  obtain ⟨a, rfl⟩ := mem_lineG_iff.mp hu
  obtain ⟨B, rfl⟩ := hf
  exact act0E_comm_act2E _ _

theorem rowG_comm_colG : ∀ u ∈ (rowG : Subgroup (T3E K)), ∀ f ∈ (colG : Subgroup (T3E K)),
    u * f = f * u := by
  rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
  exact act1E_comm_act2E _ _

theorem lineG_comm_rowG_colG : ∀ u ∈ (lineG : Subgroup (T3E K)),
    ∀ z ∈ (rowG ⊔ colG : Subgroup (T3E K)), u * z = z * u := by
  intro u hu z hz
  obtain ⟨f, hf, x, hx, rfl⟩ := fu_mem_sup rowG_comm_colG hz
  calc u * (f * x) = (u * f) * x := by rw [mul_assoc]
    _ = (f * u) * x := by rw [lineG_comm_rowG u hu f hf]
    _ = f * (u * x) := by rw [mul_assoc]
    _ = f * (x * u) := by rw [lineG_comm_colG u hu x hx]
    _ = (f * x) * u := by rw [mul_assoc]

theorem unip_sq (u : T3E K) (hu : u ∈ (lineG : Subgroup (T3E K))) : u * u = 1 := by
  obtain ⟨a, rfl⟩ := mem_lineG_iff.mp hu
  rw [← map_mul, unipSL_mul, CharTwo.add_self_eq_zero, unipSL_zero, map_one]

structure CoreData (κ : K) (γ : T3E K) (𝔸 : Subgroup (T3E K)) : Prop where
  hγ : γ ∈ Ok κ
  hAO : 𝔸 ≤ Ok κ
  hAc : ∀ a ∈ 𝔸, ∀ x ∈ colG, a * x = x * a
  hAinf : 𝔸 ⊓ colG = ⊥
  hAsup : 𝔸 ⊔ colG = (rowG ⊔ colG).map (cjH γ)
  hAsimple : IsSimpleGroup ↥𝔸
  hAn : ¬ IsMulCommutative ↥𝔸
  hAcard : Nat.card ↥𝔸 = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K)
  hy : ∃ y ∈ 𝔸, NotTwoPow y
  hN' : lineG.map (cjH γ) ≤ lineG ⊔ rowG
  hne : lineG.map (cjH γ) ≠ lineG
  hNN : lineG ≤ lineG.map (cjH γ) ⊔ (rowG ⊔ colG).map (cjH γ)

variable {κ : K} {γ : T3E K} {𝔸 : Subgroup (T3E K)}

theorem cjH_mem_Ok (hγ : γ ∈ Ok κ) {g : T3E K} (hg : g ∈ Ok κ) : cjH γ g ∈ Ok κ :=
  mul_mem (mul_mem hγ hg) (inv_mem hγ)

theorem lineG_conj_TI (D : CoreData κ γ 𝔸) :
    lineG.map (cjH γ) ⊓ lineG = ⊥ := by
  rcases lineG_conj_inf_or γ with h | h
  · rw [inf_comm]; exact h
  · exact absurd h D.hne

theorem CoreData.claimB (hKF11a : Sp4InvolutionStatement) (hK : 4 ≤ Nat.card K)
    (D : CoreData κ γ 𝔸) : κ = 0 ∧ lineG.map (cjH γ) ≤ rowG := by
  obtain ⟨y, hy𝔸, hy2⟩ := D.hy
  have hlineO : (lineG : Subgroup (T3E K)) ≤ Ok κ := lineG_le_Ok κ
  refine ct1_rows hKF11a hK κ (lineG.map (cjH γ)) ?_ ?_ ?_ ?_ (lineG_conj_TI D) y
    (D.hAO hy𝔸) (D.hAc y hy𝔸) ?_ hy2
  · rintro _ ⟨u, hu, rfl⟩
    exact cjH_mem_Ok D.hγ (hlineO hu)
  · rw [Subgroup.card_map_of_injective (cjH_injective γ), card_lineG]
    exact hK
  · intro n hn
    obtain ⟨u, hu, f, hf, rfl⟩ := fu_mem_sup lineG_comm_rowG (D.hN' hn)
    exact ⟨u, hu, f, hf, rfl⟩
  · rintro _ ⟨u, hu, rfl⟩
    rw [← map_mul, unip_sq u hu, map_one]
  · rintro _ ⟨u, hu, rfl⟩
    have hyz : y ∈ (rowG ⊔ colG).map (cjH γ) := D.hAsup ▸ Subgroup.mem_sup_left hy𝔸
    obtain ⟨z, hz, rfl⟩ := hyz
    rw [← map_mul, ← map_mul, lineG_comm_rowG_colG u hu z hz]

theorem lineG_conj_comm_sup (D : CoreData κ γ 𝔸) :
    ∀ u ∈ lineG.map (cjH γ), ∀ p ∈ 𝔸 ⊔ colG, u * p = p * u := by
  rintro _ ⟨u, hu, rfl⟩ p hp
  have hp' : p ∈ (rowG ⊔ colG).map (cjH γ) := D.hAsup ▸ hp
  obtain ⟨z, hz, rfl⟩ := hp'
  rw [← map_mul, ← map_mul, lineG_comm_rowG_colG u hu z hz]

theorem CoreData.lineG_split (hK : 4 ≤ Nat.card K) (D : CoreData κ γ 𝔸) :
    ∀ n ∈ (lineG : Subgroup (T3E K)), ∃ u ∈ lineG.map (cjH γ), ∃ a ∈ 𝔸, n = u * a := by
  intro n hn
  have h1 : n ∈ lineG.map (cjH γ) ⊔ (𝔸 ⊔ colG) := by
    have := D.hNN hn
    rwa [← D.hAsup] at this
  obtain ⟨u, hu, p, hp, rfl⟩ := fu_mem_sup (lineG_conj_comm_sup D) h1
  obtain ⟨a, ha, x, hx, rfl⟩ := fu_mem_sup D.hAc hp
  haveI := simple_colG (K := K) hK
  have hxz : ∀ z ∈ (colG : Subgroup (T3E K)), x * z = z * x := by
    intro z hz
    have hn' := lineG_comm_colG _ hn z hz
    have hu_z : u * z = z * u := lineG_conj_comm_sup D u hu z (Subgroup.mem_sup_right hz)
    have ha_z : a * z = z * a := D.hAc a ha z hz
    apply mul_left_cancel (a := u * a)
    calc u * a * (x * z) = u * (a * x) * z := by simp only [mul_assoc]
      _ = z * (u * (a * x)) := hn'
      _ = (z * u) * (a * x) := by simp only [mul_assoc]
      _ = (u * z) * (a * x) := by rw [hu_z]
      _ = u * (z * a) * x := by simp only [mul_assoc]
      _ = u * (a * z) * x := by rw [ha_z]
      _ = u * a * (z * x) := by simp only [mul_assoc]
  have hx1 : x = 1 := fu_eq_one_of_central not_comm_colG hx hxz
  exact ⟨u, hu, a, ha, by rw [hx1, mul_one]⟩

theorem CoreData.claimC (hKF11a : Sp4InvolutionStatement) (hK : 4 ≤ Nat.card K)
    (D : CoreData κ γ 𝔸) : lineG ≤ 𝔸 := by
  haveI := D.hAsimple
  haveI := simple_colG (K := K) hK
  haveI := simple_rowG (K := K) hK
  set c' : T3E K →* T3E K := cjH γ⁻¹ with hc'
  have hc'inj : Function.Injective c' := cjH_injective γ⁻¹
  have hinfmap : ∀ (H₁ H₂ : Subgroup (T3E K)), (H₁ ⊓ H₂).map c' = H₁.map c' ⊓ H₂.map c' :=
    fun H₁ H₂ => Subgroup.map_inf H₁ H₂ c' hc'inj
  have hfu : (𝔸.map c' = rowG ∧ colG.map c' = colG) ∨ (𝔸.map c' = colG ∧ colG.map c' = rowG) := by
    haveI : IsSimpleGroup ↥(𝔸.map (MulAut.conj γ⁻¹).toMonoidHom) :=
      simple_map (MulAut.conj γ⁻¹) 𝔸
    haveI : IsSimpleGroup ↥(colG.map (MulAut.conj γ⁻¹).toMonoidHom) :=
      simple_map (MulAut.conj γ⁻¹) colG
    refine factor_unique (F₁ := rowG) (F₂ := colG) (F₁' := 𝔸.map c') (F₂' := colG.map c')
      rowG_comm_colG ?_ rowG_inf_colG ?_ ?_ not_comm_rowG not_comm_colG
      (not_comm_map (MulAut.conj γ⁻¹) 𝔸 D.hAn) (not_comm_map (MulAut.conj γ⁻¹) colG not_comm_colG)
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨x, hx, rfl⟩
      rw [← map_mul, ← map_mul, D.hAc a ha x hx]
    · rw [← hinfmap, D.hAinf, Subgroup.map_bot]
    · rw [← Subgroup.map_sup, D.hAsup, Subgroup.map_map]
      have : c'.comp (cjH γ) = MonoidHom.id _ := MonoidHom.ext fun g => cjH_inv_cjH γ g
      rw [this, Subgroup.map_id]
  have hconj : ∀ u ∈ (lineG : Subgroup (T3E K)), cjH γ u ∈ lineG.map (cjH γ) :=
    fun u hu => ⟨u, hu, rfl⟩
  have hTI : lineG.map c' ⊓ lineG = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨⟨u, hu, rfl⟩, hxl⟩
    have h1 : cjH γ (c' u) ∈ lineG.map (cjH γ) ⊓ lineG :=
      ⟨⟨c' u, hxl, rfl⟩, by rw [hc', cjH_cjH_inv]; exact hu⟩
    rw [lineG_conj_TI D, Subgroup.mem_bot] at h1
    have : c' u = 1 := by
      have := congrArg (cjH γ⁻¹) h1
      rwa [cjH_inv_cjH, map_one] at this
    exact this
  have h𝒩O : lineG.map c' ≤ Ok κ := by
    rintro _ ⟨u, hu, rfl⟩
    exact cjH_mem_Ok (inv_mem D.hγ) (lineG_le_Ok κ hu)
  have h4 : 4 ≤ Nat.card (lineG.map c') := by
    rw [Subgroup.card_map_of_injective hc'inj, card_lineG]
    exact hK
  have hsq : ∀ n ∈ lineG.map c', n * n = 1 := by
    rintro _ ⟨u, hu, rfl⟩
    rw [← map_mul, unip_sq u hu, map_one]
  obtain ⟨r, hr, hr2⟩ := exists_notTwoPow_rowG (K := K) hK
  have hyO : c' r ∈ Ok κ := cjH_mem_Ok (inv_mem D.hγ) (rowG_le_Ok κ hr)
  have hy2 : NotTwoPow (c' r) := notTwoPow_map c' hc'inj hr2
  have hyn : ∀ n ∈ lineG.map c', c' r * n = n * c' r := by
    rintro _ ⟨u, hu, rfl⟩
    rw [← map_mul, ← map_mul, lineG_comm_rowG u hu r hr]
  have hsplit : ∀ n ∈ lineG.map c', ∃ u ∈ lineG, ∃ f ∈ 𝔸.map c', n = u * f := by
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨u', ⟨u₀, hu₀, rfl⟩, a, ha, rfl⟩ := D.lineG_split hK m hm
    exact ⟨u₀, hu₀, c' a, ⟨a, ha, rfl⟩, by rw [map_mul, hc', cjH_inv_cjH]⟩
  have hback : ∀ F : Subgroup (T3E K), 𝔸.map c' = F → lineG.map c' ≤ F → lineG ≤ 𝔸 := by
    intro F hF hle u hu
    have h1 : c' u ∈ 𝔸.map c' := by rw [hF]; exact hle ⟨u, hu, rfl⟩
    obtain ⟨a, ha, hau⟩ := h1
    rw [← hc'inj hau]
    exact ha
  rcases hfu with ⟨hA, hC⟩ | ⟨hA, hC⟩
  · refine hback rowG hA ?_
    refine (ct1_rows hKF11a hK κ (lineG.map c') h𝒩O h4 ?_ hsq hTI (c' r) hyO ?_ hyn hy2).2
    · intro n hn
      obtain ⟨u, hu, f, hf, rfl⟩ := hsplit n hn
      exact ⟨u, hu, f, hA ▸ hf, rfl⟩
    · intro g hg
      have hg' : g ∈ colG.map c' := by rw [hC]; exact hg
      obtain ⟨g₁, hg₁, rfl⟩ := hg'
      rw [← map_mul, ← map_mul, rowG_comm_colG r hr g₁ hg₁]
  · refine hback colG hA ?_
    refine (ct1_cols hKF11a hK κ (lineG.map c') h𝒩O h4 ?_ hsq hTI (c' r) hyO ?_ hyn hy2).2
    · intro n hn
      obtain ⟨u, hu, f, hf, rfl⟩ := hsplit n hn
      exact ⟨u, hu, f, hA ▸ hf, rfl⟩
    · intro g hg
      have hg' : g ∈ colG.map c' := by rw [hC]; exact hg
      obtain ⟨g₁, hg₁, rfl⟩ := hg'
      rw [← map_mul, ← map_mul, rowG_comm_colG r hr g₁ hg₁]

end CoreThm

end Triple

end CFSG.RankThree.GF2n.Smith81.Smith23E1
