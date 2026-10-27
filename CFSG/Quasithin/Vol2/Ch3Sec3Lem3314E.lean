module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3314D

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.Ins314

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {U Z : Subgroup V}

@[expose] def diag1 : Multiplicative L3.Vec →* Multiplicative (Fin 1 → L3.Vec) where
  toFun w := Multiplicative.ofAdd fun _ => Multiplicative.toAdd w
  map_one' := rfl
  map_mul' _ _ := rfl

theorem diag1_injective : Function.Injective diag1 := by
  intro x y h
  have := congrFun (congrArg Multiplicative.toAdd h) 0
  exact Multiplicative.toAdd.injective this

theorem diag1_surjective : Function.Surjective diag1 := by
  intro y
  refine ⟨Multiplicative.ofAdd (Multiplicative.toAdd y 0), ?_⟩
  apply Multiplicative.toAdd.injective
  funext i
  rw [Subsingleton.elim i 0]
  rfl

theorem Coord.of_binaryNatural (h : BinaryNaturalSL H U Z 3 1) : Nonempty (Coord H U Z 1) := by
  obtain ⟨D⟩ := h.toL3Coord
  have hbij : Function.Bijective D.π := ⟨D.π_injective, D.π_surj⟩
  refine ⟨⟨MulEquiv.ofBijective D.π hbij, diag1.comp D.β,
    diag1_surjective.comp D.β_surj, fun u => ?_, D.Z_le, fun g u hu => D.inv_U _ g.2 u hu,
    fun γ u hu => ?_⟩⟩
  · rw [← D.ker_β u]
    show diag1 (D.β u) = 1 ↔ D.β u = 1
    exact map_eq_one_iff _ diag1_injective
  · have e := D.equi γ u hu
    show diag1 (D.β ⟨((D.π γ : ↥H) : MulAut V) (u : V), hu⟩) = _
    rw [e]
    rfl

@[expose] def pair2 (x y : Multiplicative L3.Vec) : Multiplicative (Fin 2 → L3.Vec) :=
  Multiplicative.ofAdd ![Multiplicative.toAdd x, Multiplicative.toAdd y]

theorem pair2_mul (x y x' y' : Multiplicative L3.Vec) :
    pair2 (x * x') (y * y') = pair2 x y * pair2 x' y' := by
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i <;> rfl

theorem pair2_eq_one_iff (x y : Multiplicative L3.Vec) : pair2 x y = 1 ↔ x = 1 ∧ y = 1 := by
  constructor
  · intro h
    have h0 := congrFun (congrArg Multiplicative.toAdd h) 0
    have h1 := congrFun (congrArg Multiplicative.toAdd h) 1
    exact ⟨Multiplicative.toAdd.injective h0, Multiplicative.toAdd.injective h1⟩
  · rintro ⟨rfl, rfl⟩
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> rfl

section DirectSum

variable {I₀ I₁ : Subgroup V} (hU : U = I₀ ⊔ I₁) (hII : I₀ ⊓ I₁ = Z) (hZ₀ : Z ≤ I₀)
  (β₀ : ↥I₀ →* Multiplicative L3.Vec) (β₁ : ↥I₁ →* Multiplicative L3.Vec)
  (hβ₀k : ∀ u : ↥I₀, β₀ u = 1 ↔ (u : V) ∈ Z) (hβ₁k : ∀ u : ↥I₁, β₁ u = 1 ↔ (u : V) ∈ Z)

include hII hβ₀k hβ₁k in
theorem pair2_eq_of_mul_eq {a a' : ↥I₀} {b b' : ↥I₁} (h : (a : V) * b = a' * b') :
    pair2 (β₀ a) (β₁ b) = pair2 (β₀ a') (β₁ b') := by
  have e : (a' : V)⁻¹ * a = b' * (b : V)⁻¹ := by
    calc (a' : V)⁻¹ * a = (a' : V)⁻¹ * ((a : V) * b) * (b : V)⁻¹ := by group
      _ = (a' : V)⁻¹ * ((a' : V) * b') * (b : V)⁻¹ := by rw [h]
      _ = b' * (b : V)⁻¹ := by group
  have hZ : (a' : V)⁻¹ * a ∈ Z := by
    rw [← hII]
    refine ⟨I₀.mul_mem (I₀.inv_mem a'.2) a.2, ?_⟩
    rw [e]
    exact I₁.mul_mem b'.2 (I₁.inv_mem b.2)
  have hZ' : (b' : V) * (b : V)⁻¹ ∈ Z := by
    rw [← e]
    exact hZ
  have h0 : β₀ a = β₀ a' := by
    have := (hβ₀k (a'⁻¹ * a)).mpr hZ
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    exact this.symm
  have h1 : β₁ b = β₁ b' := by
    have := (hβ₁k (b' * b⁻¹)).mpr hZ'
    rw [map_mul, map_inv, mul_inv_eq_one] at this
    exact this.symm
  rw [h0, h1]

include hU in
theorem exists_decomp (u : ↥U) : ∃ a : ↥I₀, ∃ b : ↥I₁, (a : V) * b = u := by
  have hu : (u : V) ∈ I₀ ⊔ I₁ := hU ▸ u.2
  obtain ⟨a, ha, b, hb, e⟩ := Subgroup.mem_sup.mp hu
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩

@[expose] noncomputable def beta2 : ↥U →* Multiplicative (Fin 2 → L3.Vec) where
  toFun u := pair2 (β₀ (Classical.choose (exists_decomp hU u)))
    (β₁ (Classical.choose (Classical.choose_spec (exists_decomp hU u))))
  map_one' := by
    have e := Classical.choose_spec (Classical.choose_spec (exists_decomp hU (1 : ↥U)))
    have h := pair2_eq_of_mul_eq hII β₀ β₁ hβ₀k hβ₁k (a' := 1) (b' := 1)
      (e.trans (by simp))
    rw [h, map_one, map_one]
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> rfl
  map_mul' u u' := by
    have e := Classical.choose_spec (Classical.choose_spec (exists_decomp hU u))
    have e' := Classical.choose_spec (Classical.choose_spec (exists_decomp hU u'))
    have e'' := Classical.choose_spec (Classical.choose_spec (exists_decomp hU (u * u')))
    rw [← pair2_mul, ← map_mul, ← map_mul]
    apply pair2_eq_of_mul_eq hII β₀ β₁ hβ₀k hβ₁k
    rw [e'']
    simp only [Subgroup.coe_mul]
    rw [mul_mul_mul_comm, e, e']

include hII hβ₀k hβ₁k in
theorem beta2_eq {u : ↥U} {a : ↥I₀} {b : ↥I₁} (h : (a : V) * b = u) :
    beta2 hU hII β₀ β₁ hβ₀k hβ₁k u = pair2 (β₀ a) (β₁ b) := by
  have e := Classical.choose_spec (Classical.choose_spec (exists_decomp hU u))
  exact pair2_eq_of_mul_eq hII β₀ β₁ hβ₀k hβ₁k (e.trans h.symm)

end DirectSum

@[expose] noncomputable def toStated : L3.Γ →* (FFModel.nat (StatedSL 3 (ZMod 2))).Gam :=
  (Matrix.SpecialLinearGroup.toGL).codRestrict _ fun g =>
    Subgroup.subset_closure (Matrix.SpecialLinearGroup.det_coe g)

theorem toStated_surjective : Function.Surjective toStated := by
  rintro ⟨A, -⟩
  have hdet : (A : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 := by
    have h1 : (Matrix.GeneralLinearGroup.det A : ZMod 2) ≠ 0 :=
      (Matrix.GeneralLinearGroup.det A).ne_zero
    have h2 : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    simpa using h2 _ h1
  refine ⟨⟨A, hdet⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rfl

theorem exists_beta_of_realizesVia {I : Subgroup V}
    {π : (FFModel.nat (StatedSL 3 (ZMod 2))).Gam →* ↥H}
    (h : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia H I Z π) :
    ∃ β : ↥I →* Multiplicative L3.Vec, Function.Surjective β ∧
      (∀ u : ↥I, β u = 1 ↔ (u : V) ∈ Z) ∧
      ∀ (γ : L3.Γ) (u : ↥I) (hu : ((π (toStated γ) : ↥H) : MulAut V) (u : V) ∈ I),
        β ⟨_, hu⟩ = Multiplicative.ofAdd (L3.act γ (Multiplicative.toAdd (β u))) := by
  obtain ⟨β, hs, hk, he⟩ := FFModel.RealizesVia.coord rfl rfl h
  exact ⟨β, hs, hk, fun γ u hu => he (toStated γ) u hu⟩

theorem pair2_toAdd (x : Multiplicative (Fin 2 → L3.Vec)) :
    pair2 (Multiplicative.ofAdd (Multiplicative.toAdd x 0))
      (Multiplicative.ofAdd (Multiplicative.toAdd x 1)) = x := by
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i <;> rfl

theorem Coord.of_directSum
    (h : DirectSumOfCopies H U Z (FFModel.nat (StatedSL 3 (ZMod 2))) 2) :
    Nonempty (Coord H U Z 2) := by
  obtain ⟨I, π, hZI, hind, hUI, hreal⟩ := h
  have hsup : (⨆ i, I i) = I 0 ⊔ I 1 := by
    refine le_antisymm (iSup_le fun i => ?_) (sup_le (le_iSup I 0) (le_iSup I 1))
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  have hU : U = I 0 ⊔ I 1 := by
    rw [← hUI, hsup]
    exact sup_eq_right.mpr (le_sup_of_le_left (hZI 0))
  have hII : I 0 ⊓ I 1 = Z := by
    have h0 := hind 0
    have hs1 : (⨆ (j : Fin 2) (_ : j ≠ 0), I j) = I 1 := by
      refine le_antisymm (iSup₂_le fun j hj => ?_) (le_iSup₂_of_le (1 : Fin 2) (by decide) le_rfl)
      fin_cases j
      · exact absurd rfl hj
      · exact le_rfl
    rwa [hs1, sup_eq_right.mpr (hZI 1)] at h0
  obtain ⟨β₀, hs₀, hk₀, he₀⟩ := exists_beta_of_realizesVia (hreal 0)
  obtain ⟨β₁, hs₁, hk₁, he₁⟩ := exists_beta_of_realizesVia (hreal 1)
  obtain ⟨hπs, -, -, hinv₀, -, -⟩ := hreal 0
  have hinv₁ := (hreal 1).2.2.2.1
  set π' : L3.Γ →* ↥H := π.comp toStated with hπ'
  have hπ's : Function.Surjective π' := hπs.comp toStated_surjective
  have hπ'i : Function.Injective π' := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    apply L3.act_ext
    intro w
    rw [L3.act_one]
    obtain ⟨u, hu⟩ := hs₀ (Multiplicative.ofAdd w)
    have hmem : ((π (toStated γ) : ↥H) : MulAut V) (u : V) ∈ I 0 := hinv₀ _ u u.2
    have h1 := he₀ γ u hmem
    have h2 : (⟨((π (toStated γ) : ↥H) : MulAut V) (u : V), hmem⟩ : ↥(I 0)) = u := by
      apply Subtype.ext
      show ((π' γ : ↥H) : MulAut V) (u : V) = u
      rw [hγ]
      rfl
    rw [h2, hu] at h1
    exact (Multiplicative.ofAdd.injective h1).symm
  have hZ₀ : Z ≤ I 0 := hZI 0
  have hdecomp : ∀ u : ↥U, ∃ a : ↥(I 0), ∃ b : ↥(I 1), (a : V) * b = u := exists_decomp hU
  refine ⟨⟨MulEquiv.ofBijective π' ⟨hπ'i, hπ's⟩, beta2 hU hII β₀ β₁ hk₀ hk₁, ?_, ?_,
    hZ₀.trans (hU ▸ le_sup_left), ?_, ?_⟩⟩
  · intro x
    obtain ⟨a, ha⟩ := hs₀ (Multiplicative.ofAdd (Multiplicative.toAdd x 0))
    obtain ⟨b, hb⟩ := hs₁ (Multiplicative.ofAdd (Multiplicative.toAdd x 1))
    have hab : (a : V) * b ∈ U := hU ▸ Subgroup.mul_mem_sup a.2 b.2
    refine ⟨⟨_, hab⟩, ?_⟩
    rw [beta2_eq hU hII β₀ β₁ hk₀ hk₁ (u := ⟨_, hab⟩) rfl, ha, hb, pair2_toAdd]
  · intro u
    obtain ⟨a, b, hab⟩ := hdecomp u
    rw [beta2_eq hU hII β₀ β₁ hk₀ hk₁ hab, pair2_eq_one_iff, hk₀, hk₁, ← hab]
    constructor
    · rintro ⟨ha, hb⟩
      exact Z.mul_mem ha hb
    · intro hu
      have hb : (b : V) = (a : V)⁻¹ * (a * b) := by group
      have ha' : (a : V) ∈ I 1 := by
        have h1 : (a : V) = (a * b : V) * (b : V)⁻¹ := by group
        rw [h1]
        exact (I 1).mul_mem ((hII ▸ inf_le_right : Z ≤ I 1) hu) ((I 1).inv_mem b.2)
      have haZ : (a : V) ∈ Z := hII ▸ ⟨a.2, ha'⟩
      refine ⟨haZ, ?_⟩
      rw [hb]
      exact Z.mul_mem (Z.inv_mem haZ) hu
  · intro g u hu
    rw [hU] at hu ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hu
    rw [map_mul]
    exact Subgroup.mul_mem_sup (hinv₀ g a ha) (hinv₁ g b hb)
  · intro γ u hu
    obtain ⟨a, b, hab⟩ := hdecomp u
    have ha : ((π (toStated γ) : ↥H) : MulAut V) (a : V) ∈ I 0 := hinv₀ _ a a.2
    have hb : ((π (toStated γ) : ↥H) : MulAut V) (b : V) ∈ I 1 := hinv₁ _ b b.2
    have hab' : (⟨_, ha⟩ : ↥(I 0)).1 * (⟨_, hb⟩ : ↥(I 1)).1 =
        ((((MulEquiv.ofBijective π' ⟨hπ'i, hπ's⟩) γ : ↥H) : MulAut V) (u : V)) := by
      show _ = ((π (toStated γ) : ↥H) : MulAut V) (u : V)
      rw [← hab, map_mul]
    rw [beta2_eq hU hII β₀ β₁ hk₀ hk₁ (u := ⟨_, hu⟩) hab', he₀ γ a ha, he₁ γ b hb,
      beta2_eq hU hII β₀ β₁ hk₀ hk₁ hab]
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> rfl

@[expose] def u4 : L3.Γ := ⟨!![1, 1, 0; 0, 1, 1; 0, 0, 1], by decide⟩

theorem u4_pow_four : u4 ^ 4 = 1 := by decide +kernel

theorem sq_eq_one_of_stated_two {K : Type} [Field K] (h2 : (2 : K) = 0)
    (g : ↥(StatedSL 2 K)) (hg : g ^ 4 = 1) : g ^ 2 = 1 := by
  have hdet : ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    have hle : StatedSL 2 K ≤ (Matrix.GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ).ker := by
      rw [StatedSL, Subgroup.closure_le]
      intro A hA
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      exact Units.ext (by simpa using hA)
    have h1 := hle g.2
    rw [MonoidHom.mem_ker] at h1
    simpa using congrArg Units.val h1
  set A : Matrix (Fin 2) (Fin 2) K := ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hA
  set t : K := A 0 0 + A 1 1 with ht
  have hsq : A * A = t • A + 1 := by
    rw [Matrix.det_fin_two] at hdet
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul, Matrix.one_apply, Fin.isValue, Fin.zero_eta, Fin.mk_one, ht] <;>
      simp <;> first | ring1 | linear_combination (-1 : K) * hdet - h2
  have h4 : A * A * (A * A) = 1 := by
    have := congrArg (fun x : ↥(StatedSL 2 K) => ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
      hg
    simpa [pow_succ, mul_assoc, hA] using this
  have htt : t + t = 0 := by rw [← two_mul, h2, zero_mul]
  have hexp : A * A * (A * A) = t ^ 2 • (A * A) + 1 := by
    calc A * A * (A * A) = (t • A + 1) * (t • A + 1) := by rw [hsq]
      _ = t ^ 2 • (A * A) + (t + t) • A + 1 := by
          simp only [add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one]
          module
      _ = t ^ 2 • (A * A) + 1 := by rw [htt, zero_smul, add_zero]
  have hz : t ^ 2 • (A * A) = 0 := add_eq_right.1 (hexp.symm.trans h4)
  have hAA : A * A ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h4
    exact zero_ne_one h4
  have ht0 : t = 0 := by
    rcases smul_eq_zero.1 hz with h | h
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
    · exact absurd h hAA
  have hA2 : A * A = 1 := by rw [hsq, ht0, zero_smul, zero_add]
  apply Subtype.ext
  apply Units.ext
  simpa [pow_two, hA] using hA2

theorem two_eq_zero_of_card {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    (2 : K) = 0 := by
  have : Fintype K := Fintype.ofFinite K
  have h0 : ((Fintype.card K : ℕ) : K) = 0 := FiniteField.cast_card_eq_zero K
  rw [← Nat.card_eq_fintype_card, hK] at h0
  push_cast at h0
  have hn : n ≠ 0 := by
    rintro rfl
    have h1 : Nat.card K = 1 := by simpa using hK
    have := Finite.one_lt_card (α := K)
    omega
  exact pow_eq_zero_iff hn |>.mp h0

theorem orderOf_u4 : orderOf u4 = 4 :=
  (orderOf_eq_iff (by norm_num)).mpr ⟨u4_pow_four, by decide +kernel⟩

theorem not_binaryNaturalSL_two (e : ↥H ≃* L3.Γ) (n : ℕ) : ¬ BinaryNaturalSL H U Z 2 n := by
  rintro ⟨K, _, _, hK, π₀, hπ⟩
  have h2 := two_eq_zero_of_card hK
  let π : ↥(StatedSL 2 K) →* ↥H := π₀
  have hπs : Function.Surjective π := hπ.1
  obtain ⟨g, hg⟩ := hπs (e.symm u4)
  have hpos := orderOf_pos g
  have h4 : 4 ∣ orderOf g := by
    have h1 : (e.symm u4) ^ orderOf g = 1 := by rw [← hg, ← map_pow, pow_orderOf_eq_one, map_one]
    have h2' : orderOf (e.symm u4) = 4 := by rw [MulEquiv.orderOf_eq, orderOf_u4]
    rw [← h2']
    exact orderOf_dvd_of_pow_eq_one h1
  obtain ⟨m, hm⟩ := h4
  have hgm : (g ^ m) ^ 4 = 1 := by rw [← pow_mul, mul_comm, ← hm, pow_orderOf_eq_one]
  have hgm2 : g ^ (m * 2) = 1 := by rw [pow_mul]; exact sq_eq_one_of_stated_two h2 (g ^ m) hgm
  have hd := orderOf_dvd_of_pow_eq_one hgm2
  rw [hm] at hd
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hm; omega
    · exact h
  have := Nat.le_of_dvd (by omega) hd
  omega

theorem not_alternatingNatural_five (e : ↥H ≃* L3.Γ) : ¬ AlternatingNatural H U Z 5 := by
  rintro ⟨π₀, hπ⟩
  let π : ↥(alternatingGroup (Fin 5)) →* ↥H := π₀
  have h1 := Nat.card_le_card_of_surjective π hπ.1
  rw [Nat.card_congr e.toEquiv, card_L3Γ] at h1
  have h2 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    rfl
  omega

theorem nonempty_equiv_of_isPSL {X : Type} [Group X] (h : CFSG.Quasithin.IsPSL 3 2 1 X) :
    Nonempty (X ≃* L3.Γ) := by
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := h
  exact ⟨e.trans (CFSG.QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two 3 F
    (by rw [hcard]; norm_num))⟩

theorem exists_coord (hP : CFSG.Quasithin.IsPSL 3 2 1 ↥H)
    (hmod : (∃ n : ℕ, BinaryNaturalSL H U Z 2 n) ∨ AlternatingNatural H U Z 5 ∨
      BinaryNaturalSL H U Z 3 1 ∨
      DirectSumOfCopies H U Z (FFModel.nat (StatedSL 3 (ZMod 2))) 2) :
    ∃ k, 0 < k ∧ Nonempty (Coord H U Z k) := by
  obtain ⟨e⟩ := nonempty_equiv_of_isPSL hP
  rcases hmod with ⟨n, hn⟩ | h5 | h31 | h2
  · exact absurd hn (not_binaryNaturalSL_two e n)
  · exact absurd h5 (not_alternatingNatural_five e)
  · exact ⟨1, one_pos, Coord.of_binaryNatural h31⟩
  · exact ⟨2, two_pos, Coord.of_directSum h2⟩

end CFSG.Quasithin.H13.Ins314
