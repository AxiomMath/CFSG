module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res2ProofXAutQuot
public import CFSG.RankThree.PartTwo.Sec20.Item20Res2ProofXAutCore

public section

namespace CFSG.RankThree.PartTwo.Sec20.Res2

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.CGT.T75N

section Torus

variable {F : Type} [Field F]

@[expose] def torSL (s : Fˣ) : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, 0; 0, (s : F), 0; 0, 0, ((s⁻¹ : Fˣ) : F)], by simp [det_fin_three]⟩

theorem torSL_mulVec (s : Fˣ) (x : Fin 3 → F) :
    (torSL s : Matrix (Fin 3) (Fin 3) F) *ᵥ x = ![x 0, (s : F) * x 1, ((s⁻¹ : Fˣ) : F) * x 2] := by
  ext i
  fin_cases i <;> simp [torSL, mulVec, dotProduct, Fin.sum_univ_three]

theorem torSL_mem_vstab (s : Fˣ) : torSL s ∈ vstab F := by
  show (torSL s : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = Pi.single 0 1
  rw [torSL_mulVec]
  ext i
  fin_cases i <;> simp

theorem torSL_mem_upperTriangular (s : Fˣ) : torSL s ∈ LinearFlag.upperTriangular 3 F := by
  rw [LinearFlag.mem_upperTriangular_iff_isUpperTriangular]
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [torSL]

theorem torSL_inv (s : Fˣ) : (torSL s)⁻¹ = torSL s⁻¹ := by
  rw [inv_eq_iff_mul_eq_one]
  apply Subtype.ext
  rw [slCoeMul, slCoeOne]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [torSL, Matrix.mul_apply, Fin.sum_univ_three]

theorem conj_torSL_uelt (s : Fˣ) (a : Fin 3 → F) (ha : a 0 = 0) :
    torSL s * uelt a ha * (torSL s)⁻¹ =
      uelt ![a 0, a 1 * ((s⁻¹ : Fˣ) : F), a 2 * (s : F)] (by simp [ha]) := by
  rw [conj_uelt (torSL_mem_vstab s) a ha]
  congr 1
  rw [torSL_inv]
  ext j
  fin_cases j <;> simp [torSL, vecMul, dotProduct, Fin.sum_univ_three]

theorem unitriangular_mulVec_two {u : SpecialLinearGroup (Fin 3) F}
    (hu : u ∈ LinearFlag.unitriangular 3 F) (x : Fin 3 → F) :
    ((u : Matrix (Fin 3) (Fin 3) F) *ᵥ x) 2 = x 2 := by
  obtain ⟨hlow, hdiag⟩ := LinearFlag.mem_unitriangular.mp hu
  simp [mulVec, dotProduct, Fin.sum_univ_three, hlow 2 0 (by decide), hlow 2 1 (by decide),
    hdiag 2]

theorem unitriangular_mulVec_one {u : SpecialLinearGroup (Fin 3) F}
    (hu : u ∈ LinearFlag.unitriangular 3 F) (x : Fin 3 → F) :
    ((u : Matrix (Fin 3) (Fin 3) F) *ᵥ x) 1 = x 1 + (u : Matrix (Fin 3) (Fin 3) F) 1 2 * x 2 := by
  obtain ⟨hlow, hdiag⟩ := LinearFlag.mem_unitriangular.mp hu
  simp [mulVec, dotProduct, Fin.sum_univ_three, hlow 1 0 (by decide), hdiag 1]

theorem transvection_one_two_mem_unitriangular (z : F) :
    SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) z ∈
      LinearFlag.unitriangular 3 F := by
  rw [LinearFlag.mem_unitriangular, SpecialLinearGroup.transvection_coe]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all
  · fin_cases i <;> simp

theorem unitriangular_le_vstab : LinearFlag.unitriangular 3 F ≤ vstab F := fun _ hu =>
  unitriangular_mulVec_e0 hu

theorem uelt_congr {a b : Fin 3 → F} (ha : a 0 = 0) (hb : b 0 = 0) (h : a = b) :
    uelt a ha = uelt b hb := by
  subst h
  rfl

@[expose] def ucolHom : Multiplicative F →* SpecialLinearGroup (Fin 3) F where
  toFun b := uelt ![0, 0, Multiplicative.toAdd b] (by simp)
  map_one' := uelt_eq_one _ (by ext i; fin_cases i <;> simp)
  map_mul' a b := by
    rw [uelt_mul]
    exact uelt_congr _ _ (by ext i; fin_cases i <;> simp)

theorem ucolHom_injective : Function.Injective (ucolHom (F := F)) := by
  intro a b h
  have := congrFun (uelt_injective (ha := by simp) (hb := by simp) h) 2
  simpa using this

end Torus

variable {G : Type} [Group G] {K V X : Subgroup G} {F : Type} [Field F] {d : NatData G K V F}

theorem mem_center_pCoreOf_iff (q : ↥(CFSG.Open.pCoreOf 2 X)) :
    q ∈ Subgroup.center ↥(CFSG.Open.pCoreOf 2 X) ↔ (q : G) ∈ zQ X := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h
    refine ⟨q.2, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
    exact congrArg Subtype.val (h ⟨a, ha⟩)
  · rintro ⟨-, h⟩ a
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp h a a.2)

theorem mk_eq_one_iff (q : ↥(CFSG.Open.pCoreOf 2 X)) :
    (q : quotZ (CFSG.Open.pCoreOf 2 X)) = 1 ↔ (q : G) ∈ zQ X := by
  rw [QuotientGroup.eq_one_iff, mem_center_pCoreOf_iff]

variable [Finite G] [Fintype F] [CharP F 2] {n : ℕ}

@[expose] noncomputable def XData.thetaW (hF : Fintype.card F = 2 ^ n) (hX : XData d X) :
    quotZ (CFSG.Open.pCoreOf 2 X) →* SpecialLinearGroup (Fin 3) F :=
  QuotientGroup.lift (Subgroup.center ↥(CFSG.Open.pCoreOf 2 X))
    (d.α.comp (Subgroup.inclusion hX.pCoreOf_le_K)) (by
      intro z hz
      have hzV : (z : G) ∈ V := hX.zQ_le hF ((mem_center_pCoreOf_iff z).mp hz)
      have : (⟨z, hX.pCoreOf_le_K z.2⟩ : ↥K) ∈ d.α.ker := by
        rw [d.ker]
        exact hzV
      exact this)

omit [CharP F 2] in
theorem XData.thetaW_mk (hF : Fintype.card F = 2 ^ n) (hX : XData d X)
    (q : ↥(CFSG.Open.pCoreOf 2 X)) :
    hX.thetaW hF (q : quotZ (CFSG.Open.pCoreOf 2 X)) = d.α ⟨q, hX.pCoreOf_le_K q.2⟩ :=
  QuotientGroup.lift_mk _ _ q

omit [CharP F 2] in
theorem XData.thetaW_conjW (hF : Fintype.card F = 2 ^ n) (hX : XData d X) {x : G} (hx : x ∈ X)
    (w : quotZ (CFSG.Open.pCoreOf 2 X)) :
    hX.thetaW hF (conjW _ (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hx) w) =
      d.α ⟨x, hX.le_K hx⟩ * hX.thetaW hF w * (d.α ⟨x, hX.le_K hx⟩)⁻¹ := by
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective w
  rw [conjW_mk, hX.thetaW_mk, hX.thetaW_mk, ← map_inv, ← map_mul, ← map_mul]
  rfl

omit [CharP F 2] in
theorem XData.exists_mk_of_thetaW_eq_one (hF : Fintype.card F = 2 ^ n) (hX : XData d X)
    {w : quotZ (CFSG.Open.pCoreOf 2 X)} (hw : hX.thetaW hF w = 1) :
    ∃ v : ↥V, w = (⟨v, hX.V_le_pCoreOf hF v.2⟩ : ↥(CFSG.Open.pCoreOf 2 X)) := by
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective w
  rw [hX.thetaW_mk] at hw
  have : (⟨q, hX.pCoreOf_le_K q.2⟩ : ↥K) ∈ d.α.ker := hw
  rw [d.ker, Subgroup.mem_subgroupOf] at this
  exact ⟨⟨q, this⟩, rfl⟩

theorem XData.mk_V_eq_one_iff (hF : Fintype.card F = 2 ^ n) (hX : XData d X) (v : ↥V) :
    ((⟨v, hX.V_le_pCoreOf hF v.2⟩ : ↥(CFSG.Open.pCoreOf 2 X)) : quotZ (CFSG.Open.pCoreOf 2 X)) =
      1 ↔ d.vec v 1 = 0 ∧ d.vec v 2 = 0 := by
  rw [mk_eq_one_iff]
  exact hX.mem_zQ_iff hF v

theorem XData.mk_V_eq_mk_V_iff (hF : Fintype.card F = 2 ^ n) (hX : XData d X) (v v' : ↥V) :
    ((⟨v, hX.V_le_pCoreOf hF v.2⟩ : ↥(CFSG.Open.pCoreOf 2 X)) : quotZ (CFSG.Open.pCoreOf 2 X)) =
      ((⟨v', hX.V_le_pCoreOf hF v'.2⟩ : ↥(CFSG.Open.pCoreOf 2 X)) :
        quotZ (CFSG.Open.pCoreOf 2 X)) ↔
      d.vec v' 1 = d.vec v 1 ∧ d.vec v' 2 = d.vec v 2 := by
  rw [mk_eq_mk_iff]
  have h := hX.mem_zQ_iff hF (v⁻¹ * v')
  rw [d.vec_mul, d.vec_inv] at h
  simp only [Pi.add_apply, Pi.neg_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
  have hmem : (v : G)⁻¹ * v' ∈ CFSG.Open.pCoreOf 2 X :=
    hX.V_le_pCoreOf hF (V.mul_mem (V.inv_mem v.2) v'.2)
  constructor
  · intro hc
    have := h.mp ⟨hmem, hc⟩
    exact ⟨by linear_combination this.1, by linear_combination this.2⟩
  · intro hc
    exact (h.mpr ⟨by rw [hc.1]; ring, by rw [hc.2]; ring⟩).2


omit [Finite G] [Fintype F] [CharP F 2] in
theorem NatData.vec_conj (d : NatData G K V F) (k : ↥K) (v : ↥V) (h : (k : G) * v * k⁻¹ ∈ V) :
    d.vec ⟨(k : G) * v * (k : G)⁻¹, h⟩ = (d.α k : Matrix (Fin 3) (Fin 3) F) *ᵥ d.vec v :=
  d.equiv k v _ rfl

@[expose] noncomputable def XData.vcolHom (hF : Fintype.card F = 2 ^ n) (hX : XData d X) :
    Multiplicative F →* quotZ (CFSG.Open.pCoreOf 2 X) where
  toFun b := ((⟨d.β.symm (Multiplicative.ofAdd (Pi.single 1 (Multiplicative.toAdd b))),
    hX.V_le_pCoreOf hF (d.β.symm _).2⟩ : ↥(CFSG.Open.pCoreOf 2 X)) :
      quotZ (CFSG.Open.pCoreOf 2 X))
  map_one' := by
    rw [mk_eq_one_iff]
    have : d.β.symm (Multiplicative.ofAdd (Pi.single 1 (Multiplicative.toAdd (1 : Multiplicative F))
      : Fin 3 → F)) = 1 := by simp
    rw [this]
    exact (zQ X).one_mem
  map_mul' a b := by
    rw [← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← Subgroup.coe_mul, ← map_mul, ← ofAdd_add, toAdd_mul, Pi.single_add]

omit [Finite G] [Fintype F] [CharP F 2] in
theorem XData.vec_vcol (b : F) :
    d.vec (d.β.symm (Multiplicative.ofAdd (Pi.single 1 b))) = Pi.single 1 b := by
  simp [NatData.vec]

theorem XData.vcolHom_injective (hF : Fintype.card F = 2 ^ n) (hX : XData d X) :
    Function.Injective (hX.vcolHom hF) := by
  rw [injective_iff_map_eq_one]
  intro b hb
  have := (hX.mk_V_eq_one_iff hF _).mp hb
  rw [XData.vec_vcol] at this
  simpa using this.1

theorem two_pow_mod_five_of_odd {n : ℕ} (hn : Odd n) : 2 ^ n % 5 = 2 ∨ 2 ^ n % 5 = 3 := by
  obtain ⟨m, rfl⟩ := hn
  induction m with
  | zero => left; norm_num
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring, pow_add, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> norm_num

theorem two_pow_sq_mod_five_of_odd {n : ℕ} (hn : Odd n) : (2 ^ n) ^ 2 % 5 = 4 := by
  obtain ⟨m, rfl⟩ := hn
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring, pow_add, mul_pow, Nat.mul_mod, ih]
    norm_num

@[expose] noncomputable def XData.cw (hX : XData d X) :
    Subgroup (quotZ (CFSG.Open.pCoreOf 2 X)) where
  carrier := {w | ∀ (p : G) (hp : p ∈ X), d.α ⟨p, hX.le_K hp⟩ ∈ LinearFlag.unitriangular 3 F →
      conjW _ (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hp) w = w}
  one_mem' := fun _ _ _ => map_one _
  mul_mem' := fun ha hb p hp hu => by rw [map_mul, ha p hp hu, hb p hp hu]
  inv_mem' := fun ha p hp hu => by rw [map_inv, ha p hp hu]

omit [Fintype F] [CharP F 2] in
theorem normalizer_le_normalizer_zQ :
    Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) ≤ Subgroup.normalizer (zQ X : Set G) := by
  intro g hg
  apply Sec20.mem_normalizer_of_map_conj_le
  rintro _ ⟨z, ⟨hzQ, hz⟩, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hzQ, Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro q hq
  have hq' : g⁻¹ * q * g ∈ CFSG.Open.pCoreOf 2 X := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) q).mp hq
    simpa using this
  have h := Subgroup.mem_centralizer_iff.mp hz _ hq'
  calc q * (g * z * g⁻¹) = g * ((g⁻¹ * q * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * q * g)) * g⁻¹ := by rw [h]
    _ = g * z * g⁻¹ * q := by group

theorem XData.mem_normalizer_of_five (hF : Fintype.card F = 2 ^ n) (hn : Odd n)
    (hX : XData d X) (hXv : vstab F ≤ (X.subgroupOf K).map d.α)
    (hcomm : ⁅CFSG.Open.pCoreOf 2 X, CFSG.Open.pCoreOf 2 X⁆ ≤ zQ X)
    {y : G} (hyX : y ∈ Subgroup.normalizer (X : Set G))
    (hyc : ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 X) (hy5 : y ^ 5 = 1) :
    y ∈ Subgroup.normalizer (V : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set Q := CFSG.Open.pCoreOf 2 X with hQ
  have hVQ : V ≤ Q := hX.V_le_pCoreOf hF
  have hVK : V ≤ K := hX.V_le.trans hX.le_K
  have hXN : ∀ {x : G}, x ∈ X → x ∈ Subgroup.normalizer (Q : Set G) := fun hx =>
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hx
  have hyQ : y ∈ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X hyX
  have hcomm' : ∀ a ∈ Q, ∀ b ∈ Q, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (Q : Set G) :=
    fun a ha b hb => (hcomm (Subgroup.commutator_mem_commutator ha hb)).2
  set θ := hX.thetaW hF with hθ
  have hpre : ∀ g ∈ vstab F, ∃ (x : G) (hx : x ∈ X), d.α ⟨x, hX.le_K hx⟩ = g := by
    intro g hg
    obtain ⟨⟨x, hxK⟩, hx, rfl⟩ := hXv hg
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
  choose tor htorX htor using fun s : Fˣ => hpre (torSL s) (torSL_mem_vstab s)
  obtain ⟨t₁, ht₁X, ht₁⟩ := hpre _ (unitriangular_le_vstab
    (transvection_one_two_mem_unitriangular (F := F) (-1)))
  have ht₁U : d.α ⟨t₁, hX.le_K ht₁X⟩ ∈ LinearFlag.unitriangular 3 F := by
    rw [ht₁]
    exact transvection_one_two_mem_unitriangular (-1)
  have hcommy : ∀ {x : G} (hx : x ∈ X) (w : quotZ Q),
      conjW Q hyQ (conjW Q (hXN hx) w) = conjW Q (hXN hx) (conjW Q hyQ w) :=
    fun hx w => conjW_comm Q hcomm' hyQ (hXN hx) (hyc _ hx) w
  have hcw_tor : ∀ (s : Fˣ), ∀ w ∈ hX.cw, conjW Q (hXN (htorX s)) w ∈ hX.cw := by
    intro s w hw p hp hpu
    have hh := htorX s
    have hq : (tor s)⁻¹ * p * tor s ∈ X := X.mul_mem (X.mul_mem (X.inv_mem hh) hp) hh
    have hqu : d.α ⟨(tor s)⁻¹ * p * tor s, hX.le_K hq⟩ ∈ LinearFlag.unitriangular 3 F := by
      have he : d.α ⟨(tor s)⁻¹ * p * tor s, hX.le_K hq⟩ =
          (d.α ⟨tor s, hX.le_K hh⟩)⁻¹ * d.α ⟨p, hX.le_K hp⟩ * d.α ⟨tor s, hX.le_K hh⟩ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [he, htor s]
      have hB := (LinearFlag.upperTriangular 3 F).inv_mem (torSL_mem_upperTriangular s)
      rw [← LinearFlag.normalizer_unitriangular] at hB
      have := (Subgroup.mem_normalizer_iff.mp hB _).mp hpu
      simpa using this
    calc conjW Q (hXN hp) (conjW Q (hXN hh) w)
        = conjW Q (Subgroup.mul_mem _ (hXN hp) (hXN hh)) w := (conjW_mul_apply Q _ _ _ w).symm
      _ = conjW Q (Subgroup.mul_mem _ (hXN hh) (hXN hq)) w := conjW_congr Q _ _ (by group) w
      _ = conjW Q (hXN hh) (conjW Q (hXN hq) w) := conjW_mul_apply Q _ _ _ w
      _ = conjW Q (hXN hh) w := by rw [hw _ hq hqu]
  have hcw_y : ∀ w ∈ hX.cw, conjW Q hyQ w ∈ hX.cw := by
    intro w hw p hp hpu
    rw [← hcommy hp, hw p hp hpu]
  let Fix : Subgroup (quotZ Q) :=
    { carrier := {w | w ∈ hX.cw ∧ conjW Q hyQ w = w}
      one_mem' := ⟨hX.cw.one_mem, map_one _⟩
      mul_mem' := fun ha hb => ⟨hX.cw.mul_mem ha.1 hb.1, by rw [map_mul, ha.2, hb.2]⟩
      inv_mem' := fun ha => ⟨hX.cw.inv_mem ha.1, by rw [map_inv, ha.2]⟩ }
  have hFixcw : Fix ≤ hX.cw := fun _ hw => hw.1
  have hFix_tor : ∀ (s : Fˣ), ∀ w ∈ Fix, conjW Q (hXN (htorX s)) w ∈ Fix :=
    fun s w hw => ⟨hcw_tor s w hw.1, by rw [hcommy (htorX s), hw.2]⟩
  have hθcw : ∀ w ∈ hX.cw, ∃ b : F, θ w = ucolHom (Multiplicative.ofAdd b) := by
    intro w hw
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective w
    obtain ⟨a, ha0, hau⟩ := exists_eq_uelt (hX.image_pCoreOf_le_urad q.2)
    have hθq : θ (q : quotZ Q) = uelt a ha0 := by rw [hθ, hX.thetaW_mk]; exact hau
    have h1 := congrArg θ (hw t₁ ht₁X ht₁U)
    rw [hθ, hX.thetaW_conjW hF ht₁X, ← hθ, hθq, ht₁,
      conj_uelt (unitriangular_le_vstab (transvection_one_two_mem_unitriangular (-1)))] at h1
    have h2 := uelt_injective h1
    have h3 : a ᵥ* ((SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide)
        (-1 : F) : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = a := by
      calc a ᵥ* ((SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide)
            (-1 : F) : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
          = (a ᵥ* (((SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide)
            (-1 : F))⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ᵥ*
              ((SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide)
            (-1 : F) : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by rw [h2]
        _ = a := by rw [vecMul_vecMul, slCoeInvMul, vecMul_one]
    rw [SpecialLinearGroup.transvection_coe, ← transvection, vecMul_transvection'] at h3
    have ha1 : a 1 = 0 := by
      have := congrFun h3 2
      simp at this
      exact this
    refine ⟨a 2, ?_⟩
    rw [hθq]
    exact uelt_congr ha0 (by simp) (by ext i; fin_cases i <;> simp [ha0, ha1])
  have hkercw : ∀ w ∈ hX.cw, θ w = 1 → ∃ b : F, w = hX.vcolHom hF (Multiplicative.ofAdd b) := by
    intro w hw hθw
    obtain ⟨v, rfl⟩ := hX.exists_mk_of_thetaW_eq_one hF hθw
    have hvK : (v : G) ∈ K := hVK v.2
    have ht₁v : t₁ * v * t₁⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (d.le_normalizer hVK (hX.le_K ht₁X)) v).mp v.2
    have h1 := hw t₁ ht₁X ht₁U
    rw [conjW_mk] at h1
    have h1' : ((⟨t₁ * v * t₁⁻¹, hVQ ht₁v⟩ : ↥Q) : quotZ Q) =
        ((⟨v, hVQ v.2⟩ : ↥Q) : quotZ Q) := h1
    have h2 := (hX.mk_V_eq_mk_V_iff hF ⟨_, ht₁v⟩ v).mp h1'
    rw [d.vec_conj ⟨t₁, hX.le_K ht₁X⟩ v ht₁v, ht₁, SpecialLinearGroup.transvection_coe,
      ← transvection, LinearFlag.transvection_mulVec] at h2
    have hv2 : d.vec v 2 = 0 := by
      have := h2.1
      simp at this
      exact this
    refine ⟨d.vec v 1, ?_⟩
    show _ = ((⟨d.β.symm (Multiplicative.ofAdd (Pi.single 1 (d.vec v 1))), _⟩ : ↥Q) : quotZ Q)
    refine (hX.mk_V_eq_mk_V_iff hF v _).mpr ?_
    rw [XData.vec_vcol]
    simp [hv2]
  have hvcol_cw : ∀ b : F, hX.vcolHom hF (Multiplicative.ofAdd b) ∈ hX.cw := by
    intro b p hp hpu
    set v := d.β.symm (Multiplicative.ofAdd (Pi.single 1 b)) with hv
    have hpv : p * v * p⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (d.le_normalizer hVK (hX.le_K hp)) v).mp v.2
    show conjW Q (hXN hp) ((⟨v, hVQ v.2⟩ : ↥Q) : quotZ Q) = ((⟨v, hVQ v.2⟩ : ↥Q) : quotZ Q)
    rw [conjW_mk]
    show ((⟨p * v * p⁻¹, hVQ hpv⟩ : ↥Q) : quotZ Q) = _
    refine (hX.mk_V_eq_mk_V_iff hF ⟨_, hpv⟩ v).mpr ?_
    rw [d.vec_conj ⟨p, hX.le_K hp⟩ v hpv, unitriangular_mulVec_one hpu,
      unitriangular_mulVec_two hpu, hv, XData.vec_vcol]
    simp
  have hθtor : ∀ (s : Fˣ) (b : F), (torSL s) * ucolHom (Multiplicative.ofAdd b) * (torSL s)⁻¹ =
      ucolHom (Multiplicative.ofAdd (b * (s : F))) := by
    intro s b
    exact (conj_torSL_uelt s (![0, 0, b] : Fin 3 → F) rfl).trans
      (uelt_congr _ (show (![0, 0, b * (s : F)] : Fin 3 → F) 0 = 0 from rfl)
        (by ext i; fin_cases i <;> simp))
  have hvtor : ∀ (s : Fˣ) (b : F), conjW Q (hXN (htorX s)) (hX.vcolHom hF (Multiplicative.ofAdd b))
      = hX.vcolHom hF (Multiplicative.ofAdd ((s : F) * b)) := by
    intro s b
    set v := d.β.symm (Multiplicative.ofAdd (Pi.single 1 b)) with hv
    have hh := htorX s
    have hhv : tor s * v * (tor s)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (d.le_normalizer hVK (hX.le_K hh)) v).mp v.2
    show conjW Q (hXN hh) ((⟨v, hVQ v.2⟩ : ↥Q) : quotZ Q) = _
    rw [conjW_mk]
    show ((⟨tor s * v * (tor s)⁻¹, hVQ hhv⟩ : ↥Q) : quotZ Q) =
      ((⟨d.β.symm (Multiplicative.ofAdd (Pi.single 1 ((s : F) * b))), _⟩ : ↥Q) : quotZ Q)
    refine (hX.mk_V_eq_mk_V_iff hF ⟨_, hhv⟩ _).mpr ?_
    rw [d.vec_conj ⟨tor s, hX.le_K hh⟩ v hhv, htor s, torSL_mulVec, hv, XData.vec_vcol,
      XData.vec_vcol]
    simp
  have hn0 : 1 ≤ n := hn.pos
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn0
  have hcardF : Nat.card (Multiplicative F) = 2 ^ n := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, hF]
  have hcard_ucol : Nat.card (ucolHom (F := F)).range = 2 ^ n := by
    rw [← Nat.card_congr (MonoidHom.ofInjective ucolHom_injective).toEquiv, hcardF]
  have hcard_vcol : Nat.card (hX.vcolHom hF).range = 2 ^ n := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (hX.vcolHom_injective hF)).toEquiv, hcardF]
  have hθv : ∀ b : F, θ (hX.vcolHom hF (Multiplicative.ofAdd b)) = 1 := by
    intro b
    show hX.thetaW hF ((⟨_, hVQ (d.β.symm _).2⟩ : ↥Q) : quotZ Q) = 1
    rw [hX.thetaW_mk]
    have : (⟨(d.β.symm (Multiplicative.ofAdd (Pi.single 1 b)) : G), hVK (d.β.symm _).2⟩ : ↥K) ∈
        d.α.ker := by
      rw [d.ker]
      exact (d.β.symm _).2
    exact this
  have hcard : ∀ R : Subgroup (quotZ Q), R ≤ hX.cw →
      (∀ (s : Fˣ), ∀ w ∈ R, conjW Q (hXN (htorX s)) w ∈ R) →
      Nat.card R = 1 ∨ Nat.card R = 2 ^ n ∨ Nat.card R = (2 ^ n) ^ 2 := by
    intro R hRcw hRtor
    have hsplit := Sec20.card_eq_card_map_mul_inf_ker θ R
    have himg : Nat.card (R.map θ) = 1 ∨ Nat.card (R.map θ) = 2 ^ n := by
      by_cases hbot : R.map θ = ⊥
      · left
        rw [hbot]
        exact Subgroup.card_bot
      · right
        obtain ⟨⟨g, ⟨w, hwR, rfl⟩⟩, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
        obtain ⟨b, hb⟩ := hθcw w (hRcw hwR)
        have hb0 : b ≠ 0 := by
          rintro rfl
          apply hg1
          apply Subtype.ext
          show θ w = 1
          rw [hb, ofAdd_zero, map_one]
        have heq : R.map θ = (ucolHom (F := F)).range := by
          apply le_antisymm
          · rintro _ ⟨w', hw', rfl⟩
            obtain ⟨b', hb'⟩ := hθcw w' (hRcw hw')
            exact ⟨_, hb'.symm⟩
          · rintro _ ⟨b', rfl⟩
            by_cases hb'0 : Multiplicative.toAdd b' = 0
            · have : b' = 1 := hb'0
              rw [this, map_one]
              exact (R.map θ).one_mem
            · let s : Fˣ := Units.mk0 (Multiplicative.toAdd b' / b) (div_ne_zero hb'0 hb0)
              refine ⟨conjW Q (hXN (htorX s)) w, hRtor s w hwR, ?_⟩
              rw [hθ, hX.thetaW_conjW hF (htorX s), ← hθ, hb, htor s, hθtor]
              congr 1
              simp only [s, Units.val_mk0]
              rw [mul_div_cancel₀ _ hb0]
              rfl
        rw [heq, hcard_ucol]
    have hker : Nat.card (R ⊓ θ.ker : Subgroup (quotZ Q)) = 1 ∨
        Nat.card (R ⊓ θ.ker : Subgroup (quotZ Q)) = 2 ^ n := by
      by_cases hbot : R ⊓ θ.ker = ⊥
      · left
        rw [hbot]
        exact Subgroup.card_bot
      · right
        obtain ⟨⟨w, hwR, hwk⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
        obtain ⟨b, rfl⟩ := hkercw w (hRcw hwR) hwk
        have hb0 : b ≠ 0 := by
          rintro rfl
          apply hw1
          apply Subtype.ext
          show hX.vcolHom hF (Multiplicative.ofAdd 0) = 1
          rw [ofAdd_zero, map_one]
        have heq : R ⊓ θ.ker = (hX.vcolHom hF).range := by
          apply le_antisymm
          · rintro w' ⟨hw'R, hw'k⟩
            obtain ⟨b', rfl⟩ := hkercw w' (hRcw hw'R) hw'k
            exact ⟨_, rfl⟩
          · rintro _ ⟨b', rfl⟩
            refine ⟨?_, hθv _⟩
            by_cases hb'0 : Multiplicative.toAdd b' = 0
            · have : b' = 1 := hb'0
              rw [this, map_one]
              exact R.one_mem
            · let s : Fˣ := Units.mk0 (Multiplicative.toAdd b' / b) (div_ne_zero hb'0 hb0)
              have h := hRtor s _ hwR
              rw [hvtor] at h
              convert h using 2
              simp only [s, Units.val_mk0]
              rw [div_mul_cancel₀ _ hb0]
              rfl
        rw [heq, hcard_vcol]
    rcases himg with h1 | h1 <;> rcases hker with h2 | h2 <;> rw [hsplit, h1, h2]
    · left; rfl
    · right; left; ring
    · right; left; ring
    · right; right; ring
  have hvcol_le : (hX.vcolHom hF).range ≤ hX.cw := by
    rintro _ ⟨b, rfl⟩
    exact hvcol_cw (Multiplicative.toAdd b)
  have hcw1 : Nat.card hX.cw ≠ 1 := by
    intro h
    have := Subgroup.card_le_of_le hvcol_le
    rw [h, hcard_vcol] at this
    omega
  have hmod : Nat.card hX.cw ≡ Nat.card Fix [MOD 5] := by
    let f : ↥hX.cw → ↥hX.cw := fun w => ⟨conjW Q hyQ w, hcw_y w w.2⟩
    have hit : ∀ (k : ℕ) (w : ↥hX.cw), ((f^[k] w : ↥hX.cw) : quotZ Q) = (conjW Q hyQ)^[k] w := by
      intro k
      induction k with
      | zero => intro w; rfl
      | succ k ih =>
        intro w
        rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply]
    have hf : f^[5] = id := by
      funext w
      apply Subtype.ext
      rw [hit, ← conjW_pow_apply, conjW_congr Q _ (Subgroup.one_mem _) hy5, conjW_one_apply]
      rfl
    have h := card_modEq_card_fixedPoints_of_iterate f hf
    have he : Nat.card (Function.fixedPoints f) = Nat.card Fix := Nat.card_congr
      { toFun := fun w => ⟨w.1.1, w.1.2, congrArg Subtype.val w.2⟩
        invFun := fun w => ⟨⟨w.1, w.2.1⟩, Subtype.ext w.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [he] at h
    exact h
  have h5 := two_pow_mod_five_of_odd hn
  have h25 := two_pow_sq_mod_five_of_odd hn
  have hFixeq : Fix = hX.cw := by
    refine Subgroup.eq_of_le_of_card_ge hFixcw (le_of_eq ?_)
    unfold Nat.ModEq at hmod
    rcases hcard hX.cw le_rfl hcw_tor with h | h | h
    · exact absurd h hcw1
    · rcases hcard Fix hFixcw hFix_tor with h' | h' | h' <;> rw [h, h'] at hmod ⊢ <;>
        first | rfl | omega
    · rcases hcard Fix hFixcw hFix_tor with h' | h' | h' <;> rw [h, h'] at hmod ⊢ <;>
        first | rfl | omega
  set v₁ := d.β.symm (Multiplicative.ofAdd (Pi.single 1 (1 : F))) with hv₁
  have hfix : conjW Q hyQ (hX.vcolHom hF (Multiplicative.ofAdd 1)) =
      hX.vcolHom hF (Multiplicative.ofAdd 1) := by
    have : hX.vcolHom hF (Multiplicative.ofAdd 1) ∈ Fix := hFixeq ▸ hvcol_cw 1
    exact this.2
  have hyv : y * v₁ * y⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hyQ v₁).mp (hVQ v₁.2)
  have hfix' : ((⟨y * v₁ * y⁻¹, hyv⟩ : ↥Q) : quotZ Q) = ((⟨v₁, hVQ v₁.2⟩ : ↥Q) : quotZ Q) := by
    have := hfix
    rw [show hX.vcolHom hF (Multiplicative.ofAdd 1) = ((⟨v₁, hVQ v₁.2⟩ : ↥Q) : quotZ Q) from rfl,
      conjW_mk] at this
    exact this
  rw [mk_eq_mk_iff] at hfix'
  have hz : (y * v₁ * y⁻¹)⁻¹ * v₁ ∈ zQ X := ⟨Q.mul_mem (Q.inv_mem hyv) (hVQ v₁.2), hfix'⟩
  have hzV := hX.zQ_le hF hz
  have hyvV : y * v₁ * y⁻¹ ∈ V := by
    have : y * v₁ * y⁻¹ = v₁ * ((y * v₁ * y⁻¹)⁻¹ * v₁)⁻¹ := by group
    rw [this]
    exact V.mul_mem v₁.2 (V.inv_mem hzV)
  have hv₁z : (v₁ : G) ∉ zQ X := by
    intro h
    have := (hX.mem_zQ_iff hF v₁).mp h
    rw [hv₁] at this
    simp [NatData.vec] at this
  have hyvz : y * v₁ * y⁻¹ ∉ zQ X := by
    intro h
    apply hv₁z
    have : (v₁ : G) = (y * v₁ * y⁻¹) * ((y * v₁ * y⁻¹)⁻¹ * v₁) := by group
    rw [this]
    exact (zQ X).mul_mem h hz
  set R' := V.map (MulAut.conj y).toMonoidHom ⊓ V with hR'
  have hzR' : zQ X ≤ R' := by
    intro z hz'
    refine ⟨⟨y⁻¹ * z * y, ?_, by simp [MulAut.conj_apply]; group⟩, hX.zQ_le hF hz'⟩
    have := (Subgroup.mem_normalizer_iff.mp
      (normalizer_le_normalizer_zQ (Subgroup.inv_mem _ hyQ)) z).mp hz'
    simp only [inv_inv] at this
    exact hX.zQ_le hF this
  have hXR' : X ≤ Subgroup.normalizer (R' : Set G) := by
    intro x hx
    apply Sec20.mem_normalizer_of_map_conj_le
    rintro _ ⟨r, ⟨⟨v, hv, rfl⟩, hrV⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hx' : y⁻¹ * x * y ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyX) x).mp hx
      simpa using this
    have hNV := d.le_normalizer hVK
    refine ⟨⟨(y⁻¹ * x * y) * v * (y⁻¹ * x * y)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hNV (hX.le_K hx')) v).mp hv,
      by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩,
      (Subgroup.mem_normalizer_iff.mp (hNV (hX.le_K hx)) _).mp hrV⟩
  rcases hX.eq_or_eq_of_invariant hF hzR' inf_le_right hXR' with h | h
  · exact absurd (h ▸ (⟨⟨v₁, v₁.2, rfl⟩, hyvV⟩ : y * v₁ * y⁻¹ ∈ R')) hyvz
  · have hle : V ≤ V.map (MulAut.conj y).toMonoidHom := by
      calc V = R' := h.symm
        _ ≤ _ := inf_le_left
    have hcard' : Nat.card (V.map (MulAut.conj y).toMonoidHom) ≤ Nat.card V := by
      rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]
    exact Sec20.mem_normalizer_of_map_conj_le (Subgroup.eq_of_le_of_card_ge hle hcard').ge

theorem XData.card_zQ (hF : Fintype.card F = 2 ^ n) (hX : XData d X) :
    Nat.card (zQ X) = Fintype.card F := by
  rw [← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun z => d.vec ⟨z, hX.zQ_le hF z.2⟩ 0
      invFun := fun b => ⟨d.β.symm (Multiplicative.ofAdd (Pi.single 0 b)), by
        refine (hX.mem_zQ_iff hF _).mpr ?_
        simp [NatData.vec]⟩
      left_inv := fun z => by
        apply Subtype.ext
        have hz := (hX.mem_zQ_iff hF ⟨z, hX.zQ_le hF z.2⟩).mp z.2
        have he := eq_smul_e0 hz.1 hz.2
        simp only
        have : d.β.symm (Multiplicative.ofAdd (Pi.single 0 (d.vec ⟨z, hX.zQ_le hF z.2⟩ 0))) =
            ⟨z, hX.zQ_le hF z.2⟩ := by
          apply d.vec_injective
          simp only [NatData.vec, MulEquiv.apply_symm_apply, toAdd_ofAdd]
          conv_rhs => rw [show Multiplicative.toAdd (d.β ⟨z, hX.zQ_le hF z.2⟩) =
            d.vec ⟨z, hX.zQ_le hF z.2⟩ from rfl, he]
          ext i
          fin_cases i <;> simp
        rw [this]
      right_inv := fun b => by simp [NatData.vec] }

theorem XData.card_pCoreOf (hF : Fintype.card F = 2 ^ n) (hX : XData d X) :
    Nat.card (CFSG.Open.pCoreOf 2 X) = Fintype.card F ^ 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.Open.pCoreOf 2 X with hQ
  set φ : ↥Q →* SpecialLinearGroup (Fin 3) F := d.α.comp (Subgroup.inclusion hX.pCoreOf_le_K)
    with hφ
  have h := Sec20.card_eq_card_map_mul_inf_ker φ ⊤
  have himg : (⊤ : Subgroup ↥Q).map φ = urad F := by
    apply le_antisymm
    · rintro _ ⟨q, -, rfl⟩
      exact hX.image_pCoreOf_le_urad q.2
    · intro u hu
      obtain ⟨q, hq, hqu⟩ := hX.exists_mem_pCoreOf_of_mem_urad hF hu
      exact ⟨⟨q, hq⟩, Subgroup.mem_top _, hqu⟩
  have hkerφ : φ.ker = V.subgroupOf Q := by
    ext q
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have : (⟨q.1, hX.pCoreOf_le_K q.2⟩ : ↥K) ∈ d.α.ker := h
      rw [d.ker] at this
      exact this
    · intro h
      have : (⟨q.1, hX.pCoreOf_le_K q.2⟩ : ↥K) ∈ V.subgroupOf K := h
      rw [← d.ker] at this
      exact this
  have hker : Nat.card ↥((⊤ : Subgroup ↥Q) ⊓ φ.ker) = Nat.card V := by
    rw [top_inf_eq, hkerφ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hX.V_le_pCoreOf hF)).toEquiv
  rw [Subgroup.card_top, himg, card_urad, hker, d.card_V, Nat.card_eq_fintype_card (α := F)] at h
  rw [h]
  ring

omit [Finite G] in
theorem card_quotZ_mul (Q : Subgroup G) :
    Nat.card (quotZ Q) * Nat.card (Q ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) =
      Nat.card Q := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥Q)]
  congr 1
  refine Nat.card_congr
    { toFun := fun z => ⟨⟨z.1, z.2.1⟩, Subgroup.mem_center_iff.mpr fun a => Subtype.ext
        (Subgroup.mem_centralizer_iff.mp z.2.2 a a.2)⟩
      invFun := fun z => ⟨z.1.1, z.1.2, Subgroup.mem_centralizer_iff.mpr fun a ha =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨a, ha⟩)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

omit [Finite G] [Fintype F] in
theorem coords_eq_zero_of_fix {M : SpecialLinearGroup (Fin 3) F} (hM : M ∈ vstab F)
    (hM3 : M ^ 3 = 1) (hMu : M ∉ urad F) {x : Fin 3 → F}
    (h1 : ((M : Matrix (Fin 3) (Fin 3) F) *ᵥ x) 1 = x 1)
    (h2 : ((M : Matrix (Fin 3) (Fin 3) F) *ᵥ x) 2 = x 2) : x 1 = 0 ∧ x 2 = 0 := by
  by_contra hcon
  have hx : (![x 1, x 2] : Fin 2 → F) ≠ 0 := by
    intro h
    apply hcon
    exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩
  obtain ⟨hc1, hc2⟩ := mulVec_one_two_of_mem_vstab hM x
  apply blkSL_ne_one_of_not_mem_urad hM hMu
  refine sl2_eq_one_of_fix (blkSL_pow_three hM hM3) hx ?_
  ext i
  fin_cases i
  · show (blkMat (M : Matrix (Fin 3) (Fin 3) F) *ᵥ ![x 1, x 2]) 0 = x 1
    simp only [blkMat, mulVec, dotProduct, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one]
    exact hc1.symm.trans h1
  · show (blkMat (M : Matrix (Fin 3) (Fin 3) F) *ᵥ ![x 1, x 2]) 1 = x 2
    simp only [blkMat, mulVec, dotProduct, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one]
    exact hc2.symm.trans h2

omit [Finite G] [Fintype F] in
theorem row_eq_zero_of_fix {M : SpecialLinearGroup (Fin 3) F} (hM : M ∈ vstab F)
    (hM3 : M ^ 3 = 1) (hMu : M ∉ urad F) {a : Fin 3 → F} (ha : a 0 = 0)
    (hfix : a ᵥ* (M : Matrix (Fin 3) (Fin 3) F) = a) : a = 0 := by
  set B := blkSL hM with hB
  obtain ⟨-, h10, h20⟩ := col_zero_of_mem_vstab hM
  by_contra hne
  have hx : (![a 1, a 2] : Fin 2 → F) ≠ 0 := by
    intro h
    apply hne
    ext i
    fin_cases i
    · exact ha
    · simpa using congrFun h 0
    · simpa using congrFun h 1
  have hfix' : (![a 1, a 2] : Fin 2 → F) ᵥ* ((B : Matrix (Fin 2) (Fin 2) F) - 1) = 0 := by
    have e1 := congrFun hfix 1
    have e2 := congrFun hfix 2
    simp only [vecMul, dotProduct, Fin.sum_univ_three, ha, zero_mul, zero_add] at e1 e2
    ext i
    fin_cases i
    · simp [hB, blkSL, blkMat, vecMul, dotProduct, Fin.sum_univ_two, Matrix.sub_apply,
        Matrix.one_apply]
      linear_combination e1
    · simp [hB, blkSL, blkMat, vecMul, dotProduct, Fin.sum_univ_two, Matrix.sub_apply,
        Matrix.one_apply]
      linear_combination e2
  have hdet : ((B : Matrix (Fin 2) (Fin 2) F) - 1).det = 0 :=
    Matrix.exists_vecMul_eq_zero_iff.mp ⟨_, hx, hfix'⟩
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hBy : (B : Matrix (Fin 2) (Fin 2) F) *ᵥ y = y := by
    rw [sub_mulVec, one_mulVec, sub_eq_zero] at hy
    exact hy
  exact blkSL_ne_one_of_not_mem_urad hM hMu (sl2_eq_one_of_fix (blkSL_pow_three hM hM3) hy0 hBy)

theorem XData.mem_normalizer_of_seven (hF : Fintype.card F = 2 ^ 1) (hX : XData d X)
    (hcomm : ⁅CFSG.Open.pCoreOf 2 X, CFSG.Open.pCoreOf 2 X⁆ ≤ zQ X)
    {c : G} (hcX : c ∈ X) (hc3 : c ^ 3 = 1) (hc1 : d.α ⟨c, hX.le_K hcX⟩ ≠ 1)
    {y : G} (hyX : y ∈ Subgroup.normalizer (X : Set G))
    (hyc : ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 X) (hy7 : y ^ 7 = 1) :
    y ∈ Subgroup.normalizer (V : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set Q := CFSG.Open.pCoreOf 2 X with hQ
  have hVQ : V ≤ Q := hX.V_le_pCoreOf hF
  have hVK : V ≤ K := hX.V_le.trans hX.le_K
  have hQK : Q ≤ K := hX.pCoreOf_le_K
  have hXN : ∀ {x : G}, x ∈ X → x ∈ Subgroup.normalizer (Q : Set G) := fun hx =>
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hx
  have hyQ : y ∈ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X hyX
  have hcomm' : ∀ a ∈ Q, ∀ b ∈ Q, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (Q : Set G) :=
    fun a ha b hb => (hcomm (Subgroup.commutator_mem_commutator ha hb)).2
  set θ := hX.thetaW hF with hθ
  set M := d.α ⟨c, hX.le_K hcX⟩ with hM
  have hMv : M ∈ vstab F := hX.image_le ⟨_, Subgroup.mem_subgroupOf.mpr hcX, rfl⟩
  have hM3 : M ^ 3 = 1 := by
    rw [hM, ← map_pow]
    have : (⟨c, hX.le_K hcX⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  have hMu : M ∉ urad F := not_mem_urad_of_pow_three hM3 hc1
  have hMi3 : M⁻¹ ^ 3 = 1 := by rw [inv_pow, hM3, inv_one]
  have hMiu : M⁻¹ ∉ urad F := fun h => hMu (by simpa using (urad F).inv_mem h)
  have hcfree : ∀ w : quotZ Q, conjW Q (hXN hcX) w = w → w = 1 := by
    intro w hw
    have hθw : θ w = 1 := by
      obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective w
      obtain ⟨a, ha0, hau⟩ := exists_eq_uelt (hX.image_pCoreOf_le_urad q.2)
      have hθq : θ (q : quotZ Q) = uelt a ha0 := by rw [hθ, hX.thetaW_mk]; exact hau
      have h1 := congrArg θ hw
      rw [hθ, hX.thetaW_conjW hF hcX, ← hθ, hθq, ← hM, conj_uelt hMv a ha0] at h1
      have h2 := uelt_injective h1
      have ha := row_eq_zero_of_fix ((vstab F).inv_mem hMv) hMi3 hMiu ha0 h2
      rw [hθq]
      exact uelt_eq_one ha0 ha
    obtain ⟨v, rfl⟩ := hX.exists_mk_of_thetaW_eq_one hF hθw
    have hcv : c * v * c⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (d.le_normalizer hVK (hX.le_K hcX)) v).mp v.2
    rw [conjW_mk] at hw
    have hw' : ((⟨c * v * c⁻¹, hVQ hcv⟩ : ↥Q) : quotZ Q) = ((⟨v, hVQ v.2⟩ : ↥Q) : quotZ Q) := hw
    have h2 := (hX.mk_V_eq_mk_V_iff hF ⟨_, hcv⟩ v).mp hw'
    rw [d.vec_conj ⟨c, hX.le_K hcX⟩ v hcv, ← hM] at h2
    have h3 := coords_eq_zero_of_fix hMv hM3 hMu h2.1.symm h2.2.symm
    exact (hX.mk_V_eq_one_iff hF v).mpr h3
  have hcardW : Nat.card (quotZ Q) = 16 := by
    have h1 := card_quotZ_mul Q
    rw [show (Q ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) = zQ X from rfl,
      hX.card_zQ hF, hX.card_pCoreOf hF, hF] at h1
    omega
  have hcommy : ∀ {x : G} (hx : x ∈ X) (w : quotZ Q),
      conjW Q hyQ (conjW Q (hXN hx) w) = conjW Q (hXN hx) (conjW Q hyQ w) :=
    fun hx w => conjW_comm Q hcomm' hyQ (hXN hx) (hyc _ hx) w
  let Fix : Subgroup (quotZ Q) :=
    { carrier := {w | conjW Q hyQ w = w}
      one_mem' := map_one _
      mul_mem' := fun ha hb => by
        show conjW Q hyQ (_ * _) = _ * _
        rw [map_mul, ha, hb]
      inv_mem' := fun ha => by
        show conjW Q hyQ (_)⁻¹ = (_)⁻¹
        rw [map_inv, ha] }
  have hmod7 : Nat.card (quotZ Q) ≡ Nat.card Fix [MOD 7] := by
    have hf : (conjW Q hyQ)^[7] = id := by
      funext w
      rw [← conjW_pow_apply, conjW_congr Q _ (Subgroup.one_mem _) hy7, conjW_one_apply]
      rfl
    have h := card_modEq_card_fixedPoints_of_iterate _ hf
    have he : Nat.card (Function.fixedPoints (conjW Q hyQ)) = Nat.card Fix := rfl
    rw [he] at h
    exact h
  have hmod3 : Nat.card Fix ≡ 1 [MOD 3] := by
    let g : ↥Fix → ↥Fix := fun w => ⟨conjW Q (hXN hcX) w, by
      show conjW Q hyQ _ = _
      rw [hcommy hcX, w.2]⟩
    have hit : ∀ (k : ℕ) (w : ↥Fix), ((g^[k] w : ↥Fix) : quotZ Q) = (conjW Q (hXN hcX))^[k] w := by
      intro k
      induction k with
      | zero => intro w; rfl
      | succ k ih =>
        intro w
        rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply]
    have hg : g^[3] = id := by
      funext w
      apply Subtype.ext
      rw [hit, ← conjW_pow_apply, conjW_congr Q _ (Subgroup.one_mem _) hc3, conjW_one_apply]
      rfl
    have h := card_modEq_card_fixedPoints_of_iterate g hg
    have he : Nat.card (Function.fixedPoints g) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => ?_⟩, ⟨⟨1, Subtype.ext (map_one _)⟩⟩⟩
      have ha := hcfree a.1.1 (congrArg Subtype.val a.2)
      have hb := hcfree b.1.1 (congrArg Subtype.val b.2)
      exact Subtype.ext (Subtype.ext (ha.trans hb.symm))
    rw [he] at h
    exact h
  have hdvd : Nat.card Fix ∣ 2 ^ 4 := by
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num, ← hcardW]
    exact Subgroup.card_subgroup_dvd_card Fix
  obtain ⟨k, hk, hkF⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hFixtop : Nat.card Fix = 16 := by
    unfold Nat.ModEq at hmod7 hmod3
    rw [hcardW, hkF] at hmod7
    rw [hkF] at hmod3 ⊢
    interval_cases k <;> simp_all
  have hFixeq : Fix = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hFixtop, hcardW]
  apply Sec20.mem_normalizer_of_map_conj_le
  rintro _ ⟨v, hv, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hfix : conjW Q hyQ ((⟨v, hVQ hv⟩ : ↥Q) : quotZ Q) = ((⟨v, hVQ hv⟩ : ↥Q) : quotZ Q) := by
    have : ((⟨v, hVQ hv⟩ : ↥Q) : quotZ Q) ∈ Fix := hFixeq ▸ Subgroup.mem_top _
    exact this
  rw [conjW_mk, mk_eq_mk_iff, coe_conjQ] at hfix
  have hyv : y * v * y⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hyQ v).mp (hVQ hv)
  have hz : (y * v * y⁻¹)⁻¹ * v ∈ zQ X := ⟨Q.mul_mem (Q.inv_mem hyv) (hVQ hv), hfix⟩
  have hzV := hX.zQ_le hF hz
  have : y * v * y⁻¹ = v * ((y * v * y⁻¹)⁻¹ * v)⁻¹ := by group
  rw [this]
  exact V.mul_mem hv (V.inv_mem hzV)

end CFSG.RankThree.PartTwo.Sec20.Res2
