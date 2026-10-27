module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem20Stmts
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem12
public import CFSG.Quasithin.Vol2.Ch12Sec2Cases
public import CFSG.Quasithin.Vol2.Ch11SecA02Simple

public section

namespace CFSG.Quasithin.H13
open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement

namespace Lem24

variable {G : Type} [Group G]

theorem det_eq_one_zmod_two {n : ℕ} (A : GL (Fin n) (ZMod 2)) :
    (A : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 := by
  have h : Matrix.GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
  have := congrArg Units.val h
  rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at this

theorem toGL_bijective_zmod_two (n : ℕ) :
    Function.Bijective (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin n) (ZMod 2) →* GL (Fin n) (ZMod 2)) := by
  refine ⟨fun a b h => ?_, fun A => ?_⟩
  · apply Matrix.SpecialLinearGroup.ext
    intro i j
    have := congrArg (fun M : GL (Fin n) (ZMod 2) => (M : Matrix (Fin n) (Fin n) (ZMod 2)) i j) h
    simpa using this
  · exact ⟨⟨(A : Matrix (Fin n) (Fin n) (ZMod 2)), det_eq_one_zmod_two A⟩, Units.ext rfl⟩

noncomputable def glEquivSL (n : ℕ) :
    GL (Fin n) (ZMod 2) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
  (MulEquiv.ofBijective _ (toGL_bijective_zmod_two n)).symm

theorem commutatorElement_mul_center {E : Type*} [Group E] {a b c d : E}
    (hc : c ∈ Subgroup.center E) (hd : d ∈ Subgroup.center E) : ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  have hc' := Subgroup.mem_center_iff.mp hc
  have hd' := Subgroup.mem_center_iff.mp hd
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev, mul_inv_rev]
  calc a * c * (b * d) * (c⁻¹ * a⁻¹) * (d⁻¹ * b⁻¹)
      = a * (c * (b * d) * c⁻¹) * a⁻¹ * (d⁻¹ * b⁻¹) := by group
    _ = a * (b * d) * a⁻¹ * (d⁻¹ * b⁻¹) := by rw [← hc' (b * d), mul_inv_cancel_right]
    _ = a * b * (d * a⁻¹) * (d⁻¹ * b⁻¹) := by group
    _ = a * b * (a⁻¹ * d) * (d⁻¹ * b⁻¹) := by rw [hd' a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem le_center_of_normal_of_ne_top {E : Type*} [Group E] (hE : CFSG.IsQuasisimple E)
    {N : Subgroup E} [hN : N.Normal] (hNt : N ≠ ⊤) : N ≤ Subgroup.center E := by
  obtain ⟨hper, hs, -⟩ := hE
  have hmap : (N.map (QuotientGroup.mk' (Subgroup.center E))).Normal :=
    hN.map _ (QuotientGroup.mk'_surjective _)
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (Subgroup.center E)))
    with h | h
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · exfalso
    apply hNt
    have hsup : ∀ x : E, ∃ y ∈ N, ∃ z ∈ Subgroup.center E, y * z = x := by
      intro x
      have hx : QuotientGroup.mk' (Subgroup.center E) x ∈
          N.map (QuotientGroup.mk' (Subgroup.center E)) := h ▸ Subgroup.mem_top _
      obtain ⟨y, hy, hyx⟩ := hx
      refine ⟨y, hy, y⁻¹ * x, ?_, by group⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
      exact hyx
    rw [eq_top_iff, ← hper.commutator_eq_top]
    rw [commutator, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨y₁, hy₁, z₁, hz₁, rfl⟩ := hsup a
    obtain ⟨y₂, hy₂, z₂, hz₂, rfl⟩ := hsup b
    rw [commutatorElement_mul_center hz₁ hz₂, commutatorElement_def]
    exact N.mul_mem (N.mul_mem (N.mul_mem hy₁ hy₂) (N.inv_mem hy₁)) (N.inv_mem hy₂)

theorem injective_of_quasisimple
    {E : Type*} [Group E] [Finite E] (hE : CFSG.IsQuasisimple E)
    (hO : ∀ N : Subgroup E, N.Normal → IsPGroup 2 N → N = ⊥) {n : ℕ} (hn : 3 ≤ n)
    {π : E →* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)} (hπ : Function.Surjective π) :
    Function.Injective π := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
    CFSG.Quasithin.Vol2.Ch11.SecA.isSimpleGroup_SL_zmod_two hn
  have hK : π.ker ≠ ⊤ := by
    intro h
    obtain ⟨g, hg⟩ := exists_ne (1 : Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    obtain ⟨x, rfl⟩ := hπ g
    exact hg ((MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top x))
  have hcen : π.ker ≤ Subgroup.center E := le_center_of_normal_of_ne_top hE hK
  have hodd : Odd (Nat.card π.ker) := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥π.ker) 2 h2
    have hz' : orderOf (z : E) = 2 := by rw [Subgroup.orderOf_coe, hz]
    have hzc : (z : E) ∈ Subgroup.center E := hcen z.2
    have hzn : (Subgroup.zpowers (z : E)).Normal := by
      refine ⟨fun x hx g => ?_⟩
      obtain ⟨k, rfl⟩ := hx
      show g * (z : E) ^ k * g⁻¹ ∈ _
      have hk : (z : E) ^ k ∈ Subgroup.center E := Subgroup.zpow_mem _ hzc k
      rw [Subgroup.mem_center_iff.mp hk g, mul_inv_cancel_right]
      exact ⟨k, rfl⟩
    have hz2 : IsPGroup 2 (Subgroup.zpowers (z : E)) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hz', pow_one]
    have hle := hO _ hzn hz2
    rw [Subgroup.zpowers_eq_bot] at hle
    rw [hle, orderOf_one] at hz'
    exact absurd hz' (by norm_num)
  obtain ⟨s, hs, -, -⟩ :=
    CFSG.SectionRank.EvenCover.even_linear_central_odd_extension_splitting (by omega) hπ hcen hodd
  have hk : ∀ a : E, (s (π a))⁻¹ * a ∈ Subgroup.center E := fun a =>
    hcen (by rw [MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel])
  have hrange : s.range = ⊤ := by
    rw [eq_top_iff, ← hE.1.commutator_eq_top, commutator, Subgroup.commutator_le]
    intro a _ b _
    have ha : a = s (π a) * ((s (π a))⁻¹ * a) := by group
    have hb : b = s (π b) * ((s (π b))⁻¹ * b) := by group
    rw [ha, hb, commutatorElement_mul_center (hk a) (hk b), ← map_commutatorElement]
    exact ⟨_, rfl⟩
  intro x y hxy
  obtain ⟨u, rfl⟩ : ∃ u, s u = x := (MonoidHom.mem_range).mp (hrange ▸ Subgroup.mem_top x)
  obtain ⟨w, rfl⟩ : ∃ w, s w = y := (MonoidHom.mem_range).mp (hrange ▸ Subgroup.mem_top y)
  rw [hs, hs] at hxy
  rw [hxy]

theorem eq_bot_of_normal_isPGroup_quotient {X : Type*} [Group X] [Finite X]
    (N : Subgroup (X ⧸ CFSG.pCore 2 X)) (hN : N.Normal) (h2 : IsPGroup 2 N) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := QuotientGroup.mk' (CFSG.pCore 2 X) with hφ
  have hNp : IsPGroup 2 (N.comap φ) := by
    rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := h2 ⟨φ x, hx⟩
    have h1 : (φ x) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [← map_pow, hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCore_isPGroup (G := X) 2 ⟨_, h1⟩
    refine ⟨k + j, Subtype.ext ?_⟩
    have h3 : (x ^ 2 ^ k) ^ 2 ^ j = 1 := congrArg Subtype.val hj
    simpa [pow_add, pow_mul] using h3
  have hle : N.comap φ ≤ CFSG.Open.pCore 2 X :=
    CFSG.LieType.BorelTits.le_pCore 2 (hN.comap φ) hNp
  rw [eq_bot_iff, ← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) N]
  calc (N.comap φ).map φ ≤ (CFSG.Open.pCore 2 X).map φ := Subgroup.map_mono hle
    _ = ⊥ := by exact QuotientGroup.map_mk'_self _

theorem nonempty_coords {V : Subgroup G} [Finite ↥V] (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hV2 : ∀ v ∈ V, v ^ 2 = 1) {n : ℕ} (hcard : Nat.card V = 2 ^ n) :
    Nonempty (↥V ≃* Multiplicative (Fin n → ZMod 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary
    (fun a b => Subtype.ext (hVc a a.2 b b.2)) (fun a => Subtype.ext (by simpa using hV2 a a.2))
    hcard

noncomputable def actSL {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G)) {n : ℕ}
    (e : ↥V ≃* Multiplicative (Fin n → ZMod 2)) :
    ↥L →* Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  (glEquivSL n).toMonoidHom.comp
    ((CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp (A4.actionOn V L hLV))

theorem actSL_eq_one_iff {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G)) {n : ℕ}
    (e : ↥V ≃* Multiplicative (Fin n → ZMod 2)) (x : ↥L) :
    actSL hLV e x = 1 ↔ (x : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [← A4.actionOn_eq_one_iff hLV x]
  simp only [actSL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]

theorem actSL_surjective {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G)) {n : ℕ}
    (e : ↥V ≃* Multiplicative (Fin n → ZMod 2)) (htop : autOn L V = ⊤) :
    Function.Surjective (actSL hLV e) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro g
  set σ : MulAut ↥V := (CFSG.SectionRank.Ccomm.elemAutEquivGL e).symm ((glEquivSL n).symm g)
  obtain ⟨x, hx⟩ := (A4.mem_autOn_iff hLV).mp (htop ▸ Subgroup.mem_top σ)
  refine ⟨x, ?_⟩
  simp only [actSL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hx, σ,
    MulEquiv.apply_symm_apply]

theorem centralizer_le_pCoreOf
    [Finite G] {T L V : Subgroup G} (hyp : Hyp1223 G T L V)
    (hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T))) {n : ℕ} (hn : 3 ≤ n)
    (e : ↥V ≃* Multiplicative (Fin n → ZMod 2)) (htop : autOn L V = ⊤) :
    L ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 L := by
  have hLV := le_normalizer_of_hyp1223 hyp
  set ρ := actSL hLV e with hρ
  have hO2 : CFSG.pCore 2 ↥L ≤ ρ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hρ, actSL_eq_one_iff]
    refine pCoreOf_le_centralizer_of_hyp1223 hyp hred ⟨x, ?_, rfl⟩
    assumption
  set π := QuotientGroup.lift (CFSG.pCore 2 ↥L) ρ hO2 with hπ
  have hπs : Function.Surjective π :=
    QuotientGroup.lift_surjective_of_surjective _ ρ (actSL_surjective hLV e htop) hO2
  have hπi := injective_of_quasisimple hyp.quasisimple (eq_bot_of_normal_isPGroup_quotient)
    hn hπs
  rintro x ⟨hxL, hxC⟩
  have h1 : ρ ⟨x, hxL⟩ = 1 := (actSL_eq_one_iff hLV e _).mpr hxC
  have h2 : (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 :=
    hπi (by rw [map_one]; exact h1)
  rw [QuotientGroup.eq_one_iff] at h2
  exact ⟨⟨x, hxL⟩, h2, rfl⟩

theorem transvAxis_ne_bot {W : Type*} [CommGroup W] (hW2 : ∀ w : W, w ^ 2 = 1)
    {A : Subgroup W} (hA : A.index = 2) {a : W} (haA : a ∈ A) (ha1 : a ≠ 1) :
    transvAxis A ≠ ⊥ := by
  classical
  have hmem : ∀ x y : W, x * y ∈ A ↔ (x ∈ A ↔ y ∈ A) := fun x y =>
    Subgroup.mul_mem_iff_of_index_two hA
  let f : W → W := fun x => if x ∈ A then x else x * a
  have hfA : ∀ x, x ∈ A → f x = x := fun x hx => ite_eq_left hx
  have hfnA : ∀ x, x ∉ A → f x = x * a := fun x hx => ite_eq_right hx
  have ha2 : a * a = 1 := by rw [← pow_two]; exact hW2 a
  have hff : ∀ x, f (f x) = x := by
    intro x
    by_cases hx : x ∈ A
    · rw [hfA x hx, hfA x hx]
    · have hxa : x * a ∉ A := fun h => hx (((hmem x a).mp h).mpr haA)
      rw [hfnA x hx, hfnA _ hxa, mul_assoc, ha2, mul_one]
  have hfmul : ∀ x y, f (x * y) = f x * f y := by
    intro x y
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ A
    · rw [hfA _ (A.mul_mem hx hy), hfA x hx, hfA y hy]
    · have hxy : x * y ∉ A := fun h => hy (((hmem x y).mp h).mp hx)
      rw [hfnA _ hxy, hfA x hx, hfnA y hy, mul_assoc]
    · have hxy : x * y ∉ A := fun h => hx (((hmem x y).mp h).mpr hy)
      rw [hfnA _ hxy, hfnA x hx, hfA y hy]
      ac_rfl
    · have hxy : x * y ∈ A := (hmem x y).mpr (iff_of_false hx hy)
      rw [hfA _ hxy, hfnA x hx, hfnA y hy, mul_mul_mul_comm, ha2, mul_one]
  let c : MulAut W :=
    { toFun := f, invFun := f, left_inv := hff, right_inv := hff, map_mul' := hfmul }
  have hc : c ∈ transvAxis A := by
    refine ⟨fun b hb => hfA b hb, fun v => ?_⟩
    show f v * v⁻¹ ∈ A
    by_cases hv : v ∈ A
    · rw [hfA v hv, mul_inv_cancel]
      exact A.one_mem
    · rw [hfnA v hv, mul_comm v a, mul_assoc, mul_inv_cancel, mul_one]
      exact haA
  intro hbot
  have hc1 : c = 1 := by
    have := hc
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  obtain ⟨v, hv⟩ : ∃ v, v ∉ A := by
    by_contra h
    have : A = ⊤ := eq_top_iff.mpr fun x _ => not_not.mp fun hx => h ⟨x, hx⟩
    rw [this, Subgroup.index_top] at hA
    exact absurd hA (by norm_num)
  have h1 : c v = v := by rw [hc1]; rfl
  have h2 : c v = v * a := hfnA v hv
  rw [h2] at h1
  exact ha1 (mul_eq_left.mp h1)

theorem exists_mul_of_mem_sup_normal {L T : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G))
    {x : G} (hx : x ∈ L ⊔ T) : ∃ l ∈ L, ∃ t ∈ T, l * t = x := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, T.one_mem, mul_one y⟩
    · exact ⟨1, L.one_mem, y, hy, one_mul y⟩
  | one => exact ⟨1, L.one_mem, 1, T.one_mem, mul_one 1⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨l, hl, t, ht, rfl⟩ := ihx
    obtain ⟨l', hl', t', ht', rfl⟩ := ihy
    refine ⟨l * (t * l' * t⁻¹), L.mul_mem hl ((Subgroup.mem_normalizer_iff.mp (hTL ht) l').mp hl'),
      t * t', T.mul_mem ht ht', by group⟩
  | inv x _ ih =>
    obtain ⟨l, hl, t, ht, rfl⟩ := ih
    refine ⟨t⁻¹ * l⁻¹ * t⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp (hTL (T.inv_mem ht)) l⁻¹).mp
      (L.inv_mem hl), t⁻¹, T.inv_mem ht, by group⟩

theorem exists_pow_eq_mul_pow {N : Subgroup G} {y c : G} (hy : y ∈ N)
    (hc : c ∈ Subgroup.normalizer (N : Set G)) (m : ℕ) : ∃ z ∈ N, (y * c) ^ m = z * c ^ m := by
  induction m with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨z, hz, hzm⟩ := ih
    have hcm : c ^ m ∈ Subgroup.normalizer (N : Set G) := Subgroup.pow_mem _ hc m
    refine ⟨z * (c ^ m * y * (c ^ m)⁻¹),
      N.mul_mem hz ((Subgroup.mem_normalizer_iff.mp hcm y).mp hy), ?_⟩
    rw [pow_succ, hzm, pow_succ]
    group

theorem commutator_mem_of_mem_pCoreOf
    [Finite G] {T L V U : Subgroup G}
    (hyp : Hyp1223 G T L V) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T))) {n : ℕ} (hn : 3 ≤ n)
    (e : ↥V ≃* Multiplicative (Fin n → ZMod 2)) (htop : autOn L V = ⊤) (hUT : U ≤ T)
    (hQU : ∀ q ∈ pCoreOf 2 (L ⊔ T), ∀ u ∈ U, ⁅q, u⁆ ∈ V) (hUV : autOn U V ≠ ⊥) :
    ∀ q ∈ pCoreOf 2 (L ⊔ T), ∀ l ∈ L, ⁅q, l⁆ ∈ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 (L ⊔ T) with hQ
  have hLV := le_normalizer_of_hyp1223 hyp
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  have hLTQ : L ⊔ T ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
  have hVconj : ∀ g ∈ L ⊔ T, ∀ v ∈ V, g * v * g⁻¹ ∈ V := fun g hg v hv =>
    (Subgroup.mem_normalizer_iff.mp (hLTV hg) v).mp hv
  let N : Subgroup G :=
    { carrier := {x | x ∈ L ⊔ T ∧ ∀ q ∈ Q, ⁅q, x⁆ ∈ V}
      one_mem' := ⟨(L ⊔ T).one_mem, fun q _ => by simp⟩
      mul_mem' := by
        rintro x y ⟨hx, hxq⟩ ⟨hy, hyq⟩
        refine ⟨(L ⊔ T).mul_mem hx hy, fun q hq => ?_⟩
        have e1 : ⁅q, x * y⁆ = ⁅q, x⁆ * (x * ⁅q, y⁆ * x⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e1]
        exact V.mul_mem (hxq q hq) (hVconj x hx _ (hyq q hq))
      inv_mem' := by
        rintro x ⟨hx, hxq⟩
        refine ⟨(L ⊔ T).inv_mem hx, fun q hq => ?_⟩
        have e1 : ⁅q, x⁻¹⁆ = x⁻¹ * ⁅q, x⁆⁻¹ * x⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e1]
        exact hVconj _ ((L ⊔ T).inv_mem hx) _ (V.inv_mem (hxq q hq)) }
  have hNLT : N ≤ L ⊔ T := fun x hx => hx.1
  have hNV : N ≤ Subgroup.normalizer (V : Set G) := hNLT.trans hLTV
  have hNconj : ∀ g ∈ L ⊔ T, ∀ x ∈ N, g * x * g⁻¹ ∈ N := by
    rintro g hg x ⟨hx, hxq⟩
    refine ⟨(L ⊔ T).mul_mem ((L ⊔ T).mul_mem hg hx) ((L ⊔ T).inv_mem hg), fun q hq => ?_⟩
    have hq' : g⁻¹ * q * g⁻¹⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hLTQ ((L ⊔ T).inv_mem hg)) q).mp hq
    have e1 : ⁅q, g * x * g⁻¹⁆ = g * ⁅g⁻¹ * q * g⁻¹⁻¹, x⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e1]
    exact hVconj g hg _ (hxq _ hq')
  have hNN : L ⊔ T ≤ Subgroup.normalizer (N : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hNconj g hg x, fun hx => ?_⟩
    have := hNconj g⁻¹ ((L ⊔ T).inv_mem hg) _ hx
    simpa [mul_assoc] using this
  have hUN : U ≤ N := fun u hu => ⟨Subgroup.mem_sup_right (hUT hu), fun q hq => hQU q hq u hu⟩
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
    CFSG.Quasithin.Vol2.Ch11.SecA.isSimpleGroup_SL_zmod_two hn
  have hsimple : IsSimpleGroup (MulAut ↥V) :=
    ((CFSG.SectionRank.Ccomm.elemAutEquivGL e).trans (glEquivSL n)).isSimpleGroup
  have hnorm : (autOn N V).Normal := by
    refine ⟨fun τ hτ σ => ?_⟩
    obtain ⟨⟨y, hyN⟩, rfl⟩ := (A4.mem_autOn_iff hNV).mp hτ
    obtain ⟨⟨l, hl⟩, hlσ⟩ := (A4.mem_autOn_iff hLV).mp (htop ▸ Subgroup.mem_top σ)
    rw [← hlσ, A4.mem_autOn_iff hNV]
    refine ⟨⟨l * y * l⁻¹, hNconj l (Subgroup.mem_sup_left hl) y hyN⟩, ?_⟩
    refine MulEquiv.ext fun v => Subtype.ext ?_
    rw [← map_inv]
    simp only [MulAut.mul_apply, A4.actionOn_apply_coe, InvMemClass.coe_inv]
    group
  have htopN : autOn N V = ⊤ := by
    have := hsimple
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (autOn N V)).resolve_left fun h => hUV ?_
    exact eq_bot_iff.mpr ((A4.autOn_mono hUN).trans h.le)
  have hC2 : ∀ c ∈ L ⊔ T, c ∈ Subgroup.centralizer (V : Set G) → ∃ k : ℕ, c ^ 2 ^ k = 1 := by
    intro c hc hcV
    obtain ⟨l, hl, t, ht, rfl⟩ := exists_mul_of_mem_sup_normal hyp.normalizes hc
    obtain ⟨k, hk⟩ := hyp.sylow.1 ⟨t, ht⟩
    have hk' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨z, hz, hzc⟩ := exists_pow_eq_mul_pow hl (hyp.normalizes ht) (2 ^ k)
    rw [hk', mul_one] at hzc
    have hzC : z ∈ L ⊓ Subgroup.centralizer (V : Set G) :=
      ⟨hz, hzc ▸ Subgroup.pow_mem _ hcV _⟩
    obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
      ⟨z, centralizer_le_pCoreOf hyp hred hn e htop hzC⟩
    refine ⟨k + j, ?_⟩
    have hj' : z ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    rw [pow_add, pow_mul, hzc, hj']
  have hLN : L ⊓ N = L := by
    refine hyp.faithful.2.1 (L ⊓ N) inf_le_left ⟨fun x hx g => ?_⟩ fun x hx => ?_
    · rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact ⟨L.mul_mem (L.mul_mem g.2 hx.1) (L.inv_mem g.2),
        hNconj g (Subgroup.mem_sup_left g.2) x hx.2⟩
    · have hσ : A4.actionOn V L hLV ⟨x, hx⟩ ∈ autOn N V := htopN ▸ Subgroup.mem_top _
      obtain ⟨⟨y, hyN⟩, hy⟩ := (A4.mem_autOn_iff hNV).mp hσ
      have hc : y⁻¹ * x ∈ Subgroup.centralizer (V : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        have h1 := congrArg (fun a : MulAut ↥V => ((a ⟨v, hv⟩ : ↥V) : G)) hy
        simp only [A4.actionOn_apply_coe] at h1
        calc v * (y⁻¹ * x) = y⁻¹ * (y * v * y⁻¹) * x := by group
          _ = y⁻¹ * (x * v * x⁻¹) * x := by rw [h1]
          _ = y⁻¹ * x * v := by group
      have hcLT : y⁻¹ * x ∈ L ⊔ T :=
        (L ⊔ T).mul_mem ((L ⊔ T).inv_mem (hNLT hyN)) (Subgroup.mem_sup_left hx)
      obtain ⟨k, hk⟩ := hC2 _ hcLT hc
      obtain ⟨z, hz, hzx⟩ := exists_pow_eq_mul_pow hyN (hNN hcLT) (2 ^ k)
      refine ⟨k, L.pow_mem hx _, ?_⟩
      have hx' : y * (y⁻¹ * x) = x := by group
      rw [← hx', hzx, hk, mul_one]
      exact hz
  intro q hq l hl
  have hlN : l ∈ L ⊓ N := by rw [hLN]; exact hl
  exact hlN.2.2 q hq

open Matrix in
theorem inf_centralizer_eq_bot {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G))
    {n : ℕ} (hn : 2 ≤ n) (e : ↥V ≃* Multiplicative (Fin n → ZMod 2)) (htop : autOn L V = ⊤) :
    V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  rintro v ⟨hvV, hvL⟩
  rw [Subgroup.mem_bot]
  by_contra hv1
  set x : Fin n → ZMod 2 := Multiplicative.toAdd (e ⟨v, hvV⟩) with hx
  have hx0 : x ≠ 0 := by
    intro h0
    apply hv1
    have h1 : e ⟨v, hvV⟩ = 1 := by
      rw [← ofAdd_toAdd (e ⟨v, hvV⟩), ← hx, h0, ofAdd_zero]
    exact congrArg Subtype.val ((MulEquiv.map_eq_one_iff e).mp h1)
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hx0
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨i, hij⟩ := exists_ne j
  set A : GL (Fin n) (ZMod 2) := Matrix.SpecialLinearGroup.toGL
    ⟨Matrix.transvection i j (1 : ZMod 2), Matrix.det_transvection_of_ne i j hij 1⟩ with hA
  set σ : MulAut ↥V := (CFSG.SectionRank.Ccomm.elemAutEquivGL e).symm A with hσ
  obtain ⟨⟨l, hl⟩, hlσ⟩ := (A4.mem_autOn_iff hLV).mp (htop ▸ Subgroup.mem_top σ)
  have hfix : σ ⟨v, hvV⟩ = ⟨v, hvV⟩ := by
    rw [← hlσ]
    apply Subtype.ext
    rw [A4.actionOn_apply_coe]
    show l * v * l⁻¹ = v
    rw [Subgroup.mem_centralizer_iff.mp hvL l hl, mul_inv_cancel_right]
  have h1 := CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec e σ ⟨v, hvV⟩
  rw [hfix, hσ, MulEquiv.apply_symm_apply, ← hx] at h1
  have h2 := congrFun h1 i
  have h3 : ((A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) i = x i + x j := by
    show (Matrix.transvection i j (1 : ZMod 2) *ᵥ x) i = x i + x j
    simp only [Matrix.transvection, Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply, true_and, add_mul, Finset.sum_add_distrib]
    simp
  rw [h3] at h2
  exact hj (by simpa using h2)

theorem blockU_eq
    [Finite G] {T L V U : Subgroup G} (hyp : Hyp1223 G T L V)
    (hVT : V ≤ T) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T))) {n : ℕ} (hn : 3 ≤ n)
    (e : ↥V ≃* Multiplicative (Fin n → ZMod 2)) (htop : autOn L V = ⊤) (hUT : U ≤ T)
    (hQU : ∀ q ∈ pCoreOf 2 (L ⊔ T), ∀ u ∈ U, ⁅q, u⁆ ∈ V) (hUV : autOn U V ≠ ⊥) :
    blockU L = V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLV := le_normalizer_of_hyp1223 hyp
  have hVL : V ≤ L := by
    rw [← commutator_eq_of_hyp1223 hyp]
    exact Lem12.commutator_le_of_le_normalizer (hVT.trans hyp.normalizes)
  have hVQ : V ≤ pCoreOf 2 L :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVL hLV (hyp.sylow.1.to_le hVT)
  have hQL : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
    Lem12.pCoreOf_le_pCoreOf_of_normal le_sup_left (sup_le Subgroup.le_normalizer hyp.normalizes)
  have hK1 := commutator_mem_of_mem_pCoreOf hyp hTV hred hn e htop hUT hQU hUV
  refine le_antisymm ?_ ?_
  · rw [blockU, blockQ, Subgroup.commutator_le]
    exact fun x hx l hl => hK1 x (hQL hx) l hl
  · calc V = ⁅V, L⁆ := (commutator_eq_of_hyp1223 hyp).symm
      _ ≤ ⁅pCoreOf 2 L, L⁆ := Subgroup.commutator_mono hVQ le_rfl

theorem isShort2 [Finite G] {T L V : Subgroup G} (hyp : Hyp1223 G T L V)
    (hVT : V ≤ T) (hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)))
    (hUL : blockU L = V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hV1 : V ≠ ⊥) :
    IsShort2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLV := le_normalizer_of_hyp1223 hyp
  have hVL : V ≤ L := by
    rw [← commutator_eq_of_hyp1223 hyp]
    exact Lem12.commutator_le_of_le_normalizer (hVT.trans hyp.normalizes)
  have hVQ : V ≤ pCoreOf 2 L :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVL hLV (hyp.sylow.1.to_le hVT)
  have hQV : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) :=
    pCoreOf_le_centralizer_of_hyp1223 hyp hred
  have hZL : blockZ L = ⊥ := by rw [blockZ, hUL, hZ]
  refine ⟨fun N _ h2 => ?_, ?_, ⟨?_, ?_⟩, Or.inl hyp.quasisimple, ⟨?_, fun W hW1 hW2 hW3 => ?_⟩⟩
  ·
    have hmap : N.map L.subtype = L := by
      refine hyp.faithful.2.1 (N.map L.subtype) (Subgroup.map_subtype_le N) ?_ fun x hx => ?_
      · have h1 : (N.map L.subtype).subgroupOf L = N :=
          Subgroup.comap_map_eq_self_of_injective L.subtype_injective N
        rw [h1]
        infer_instance
      · obtain ⟨k, hk⟩ := h2 (QuotientGroup.mk ⟨x, hx⟩)
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
        exact ⟨k, ⟨_, hk, rfl⟩⟩
    rw [eq_top_iff]
    intro y _
    have hy : (y : G) ∈ N.map L.subtype := by rw [hmap]; exact y.2
    obtain ⟨z, hz, hzy⟩ := hy
    rwa [Subtype.ext hzy] at hz
  · exact (quasithinGenFitting_eq_pCoreOf_iff L 2).mp hyp.faithful.2.2.1
  · rw [hUL, blockQ]
    exact le_inf hVQ (Subgroup.le_centralizer_iff.mp hQV)
  · intro x hx
    rw [hUL] at hx
    simpa using congrArg Subtype.val (sq_eq_one_of_hyp1223 hyp hred ⟨x, hx⟩)
  · rw [hZL, hUL]
    exact bot_lt_iff_ne_bot.mpr hV1
  · rw [hZL] at hW1 ⊢
    rw [hUL] at hW2 ⊢
    rw [← hZ]
    exact irreducible_of_hyp1223 hyp W (hZ ▸ hW1) hW2 hW3

open Matrix in
theorem isMatrixBlockType [Finite G] {T L V : Subgroup G} (hyp : Hyp1223 G T L V)
    (hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T))) {n : ℕ}
    (e : ↥V ≃* Multiplicative (Fin n → ZMod 2)) (htop : autOn L V = ⊤)
    (hCL : L ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 L)
    (hUL : blockU L = V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    IsMatrixBlockType L (CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLV := le_normalizer_of_hyp1223 hyp
  have hQV : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) :=
    pCoreOf_le_centralizer_of_hyp1223 hyp hred
  set ψ := CFSG.SectionRank.Ccomm.elemAutEquivGL e with hψ
  set α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2)) :=
    (ψ.toMonoidHom.comp (A4.actionOn V L hLV)).codRestrict _
      (fun x => Subgroup.subset_closure (det_eq_one_zmod_two _)) with hα
  have hαv : ∀ x : ↥L, ((α x : ↥(CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2))) :
      GL (Fin n) (ZMod 2)) = ψ (A4.actionOn V L hLV x) := fun _ => rfl
  refine ⟨α, fun A => ?_, ?_, ?_⟩
  · obtain ⟨⟨l, hl⟩, hlσ⟩ := (A4.mem_autOn_iff hLV).mp (htop ▸ Subgroup.mem_top (ψ.symm A))
    refine ⟨⟨l, hl⟩, Subtype.ext ?_⟩
    rw [hαv, hlσ, MulEquiv.apply_symm_apply]
  · ext x
    rw [MonoidHom.mem_ker]
    have h1 : α x = 1 ↔ (x : G) ∈ Subgroup.centralizer (V : Set G) := by
      rw [← A4.actionOn_eq_one_iff hLV x, ← MulEquiv.map_eq_one_iff ψ, ← hαv]
      exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
    rw [h1]
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := hCL ⟨x.2, hx⟩
      rwa [Subtype.ext hyx] at hy
    · intro hx
      exact hQV ⟨x, hx, rfl⟩
  · refine ⟨e.toMonoidHom.comp (MulEquiv.subgroupCongr hUL).toMonoidHom,
      (e.surjective.comp (MulEquiv.subgroupCongr hUL).surjective), ?_, ?_⟩
    · have hZL : blockZ L = ⊥ := by rw [blockZ, hUL, hZ]
      rw [hZL, Subgroup.bot_subgroupOf, MonoidHom.ker_eq_bot_iff]
      exact e.injective.comp (MulEquiv.subgroupCongr hUL).injective
    · intro ℓ u v huv
      have h1 := CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec e (A4.actionOn V L hLV ℓ)
        (MulEquiv.subgroupCongr hUL u)
      rw [hαv]
      show Multiplicative.toAdd (e (MulEquiv.subgroupCongr hUL v)) =
        ((ψ (A4.actionOn V L hLV ℓ) : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
          Multiplicative.toAdd (e (MulEquiv.subgroupCongr hUL u))
      rw [h1]
      congr 2
      apply Subtype.ext
      rw [A4.actionOn_apply_coe]
      exact huv

end Lem24

open Lem24

theorem lem12224Block_of
    (h1222 : Stmt12_2_2) : Lem12224Block := by
  intro G _ _ T L V H P U I h n p hyp hNE hchain
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hall⟩ := ((h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow).resolve_left
    hyp.notAlt) L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, -, -⟩ := hall V hyp.irrPlus
  obtain ⟨hHs, -, hn, hV, -, htop, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hidx, ⟨hcomm, htr⟩,
    hUO, -, -, -, -, -, -, -, hQU⟩ := hchain
  have hn3 : 3 ≤ n := by omega
  have hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥V) ⟨y, hy⟩)
  have hV2' : ∀ w : ↥V, w ^ 2 = 1 := sq_eq_one_of_hyp1223 hyp hred
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := fun v hv => by
    simpa using congrArg Subtype.val (hV2' ⟨v, hv⟩)
  obtain ⟨e⟩ := nonempty_coords hVc hV2 hV
  have hUT : U ≤ T := hUO.trans
    (B6.pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hHs.1.1))
  have hQU' : ∀ q ∈ pCoreOf 2 (L ⊔ T), ∀ u ∈ U, ⁅q, u⁆ ∈ V := fun q hq u hu =>
    (hQU (Subgroup.commutator_mem_commutator hq hu)).2
  have hA : ((U ⊓ V).subgroupOf V).index = 2 := hidx
  have hA1 : (U ⊓ V).subgroupOf V ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.index_bot, hV] at hA
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    omega
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
  have hUV : autOn U V ≠ ⊥ := by
    rw [htr]
    exact transvAxis_ne_bot hV2' hA a.2 (fun h => ha1 (Subtype.ext h))
  have hUL := blockU_eq hyp hVT hTV hred hn3 e htop hUT hQU' hUV
  have hZ := inf_centralizer_eq_bot (le_normalizer_of_hyp1223 hyp) (by omega) e htop
  have hCL := centralizer_le_pCoreOf hyp hred hn3 e htop
  have hV1 : V ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hV
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
    omega
  exact ⟨isShort2 hyp hVT hred hUL hZ hV1, isMatrixBlockType hyp hred e htop hCL hUL hZ⟩
end CFSG.Quasithin.H13
