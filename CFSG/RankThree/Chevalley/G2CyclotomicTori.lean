module

public import CFSG.RankThree.Chevalley.G2SplitPrimeToralCentralizers
public import CFSG.RankThree.Chevalley.G2F4FiniteFieldFixedMatrices
public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
public import CFSG.LieType.AlgebraicGroups.AllCharacteristicLang
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.Timmesfeld.ExceptionalOrders
  CFSG.LieType.AlgebraicGroups

theorem T0_equations_iff {M : Type*} [CommGroup M] (q k : ℤ) (hk : k = 1 ∨ k = 2) (c₁ c₂ : M) :
    (c₁ ^ (3 - k) * c₂ ^ (3 : ℤ) = c₁ ^ q ∧ c₁⁻¹ * c₂ ^ (-k) = c₂ ^ q) ↔
      (c₁ = c₂ ^ (-(q + k)) ∧ c₂ ^ (q ^ 2 + (2 * k - 3) * q + 1) = 1) := by
  have hD : q ^ 2 + (2 * k - 3) * q + 1 = (-(q + k) * (3 - k) + 3) - (-(q + k) * q) := by
    rcases hk with rfl | rfl <;> ring
  constructor
  · rintro ⟨h1, h2⟩
    have hc₁ : c₁ = c₂ ^ (-(q + k)) := by
      have : c₁⁻¹ = c₂ ^ (q + k) := by
        rw [zpow_add, ← h2, zpow_neg, inv_mul_cancel_right]
      rw [← inv_inv c₁, this, zpow_neg]
    refine ⟨hc₁, ?_⟩
    rw [hc₁, ← zpow_mul, ← zpow_mul, ← zpow_add] at h1
    rw [hD, zpow_sub, h1, mul_inv_cancel]
  · rintro ⟨hc₁, hd⟩
    subst hc₁
    constructor
    · rw [← zpow_mul, ← zpow_mul, ← zpow_add]
      have : -(q + k) * (3 - k) + 3 = (q ^ 2 + (2 * k - 3) * q + 1) + -(q + k) * q := by
        rw [hD]; ring
      rw [this, zpow_add, hd, one_mul]
    · rw [← zpow_neg, ← zpow_add]
      congr 1
      ring

variable {L : Type} [Field L]

theorem rootChar_G2 (c : Fin Tag.G2.rank → Lˣ) (v : Fin Tag.G2.rank → ℤ) :
    rootChar c v = c g2ia ^ v g2ia * c g2ir ^ v g2ir := by
  rw [rootChar]
  exact Fin.prod_univ_two (fun i => c i ^ v i)

theorem rootChar_pow_tuple {τ : Tag} (c : Fin τ.rank → Lˣ) (m : ℕ) (v : Fin τ.rank → ℤ) :
    rootChar (c ^ m) v = rootChar c v ^ m := by
  rw [rootChar, rootChar, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.pow_apply, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]

theorem entrywise_frob_rootDiagUnit {τ : Tag} (F : L →+* L) {q : ℕ}
    (hF : ∀ c, F c = c ^ q) (c : Fin τ.rank → Lˣ) :
    Units.map (entrywiseHom F) (rootDiagUnit τ c) = rootDiagUnit τ (c ^ q) := by
  refine Units.ext ?_
  rw [Units.coe_map]
  change entrywise F (rootDiag c) = rootDiag (c ^ q)
  rw [entrywise_rootDiag]
  congr 1
  funext i
  refine Units.ext ?_
  simp [hF]

theorem conj_frob_rootDiagUnit_eq_iff {τ : Tag} (F : L →+* L) {q : ℕ} (hF : ∀ c, F c = c ^ q)
    (w : WeylGroup τ) (c : Fin τ.rank → Lˣ) :
    canonicalRep (coxeterSystem τ) L w * Units.map (entrywiseHom F) (rootDiagUnit τ c) *
        (canonicalRep (coxeterSystem τ) L w)⁻¹ = rootDiagUnit τ c ↔
      ∀ v, rootChar c (w • v) = rootChar c v ^ q := by
  rw [entrywise_frob_rootDiagUnit F hF, eq_comm, rootDiagUnit_eq_conj_canonicalRep_iff]
  simp only [rootChar_pow_tuple]

theorem g2a_ia : g2a g2ia = 1 := rfl

theorem g2a_ir : g2a g2ir = 0 := rfl

theorem g2r_ia : g2r g2ia = 0 := rfl

theorem g2r_ir : g2r g2ir = 1 := rfl

theorem g2_eq_smul_add (v : Fin Tag.G2.rank → ℤ) : v = v g2ia • g2a + v g2ir • g2r := by
  funext j
  rcases fin_G2_cases j with rfl | rfl <;> simp [g2a_ia, g2a_ir, g2r_ia, g2r_ir]

theorem rootChar_g2a (c : Fin Tag.G2.rank → Lˣ) : rootChar c g2a = c g2ia := by
  rw [rootChar_G2, g2a_ia, g2a_ir, zpow_one, zpow_zero, mul_one]

theorem rootChar_g2r (c : Fin Tag.G2.rank → Lˣ) : rootChar c g2r = c g2ir := by
  rw [rootChar_G2, g2r_ia, g2r_ir, zpow_zero, zpow_one, one_mul]

theorem zpow_natCast_zpow_comm {M : Type*} [CommGroup M] (x : M) (m : ℤ) (q : ℕ) :
    (x ^ (q : ℤ)) ^ m = (x ^ m) ^ q := by
  rw [← zpow_mul, ← zpow_natCast (x ^ m), ← zpow_mul, mul_comm]

theorem forall_rootChar_iff_G2 {c : Fin Tag.G2.rank → Lˣ} {q : ℕ} {w : WeylGroup .G2} {k : ℤ}
    (hw1 : w • g2a = (3 - k) • g2a + (3 : ℤ) • g2r)
    (hw2 : w • g2r = (-1 : ℤ) • g2a + (-k) • g2r) :
    (∀ v, rootChar c (w • v) = rootChar c v ^ q) ↔
      (c g2ia ^ (3 - k) * c g2ir ^ (3 : ℤ) = c g2ia ^ (q : ℤ) ∧
        (c g2ia)⁻¹ * c g2ir ^ (-k) = c g2ir ^ (q : ℤ)) := by
  have e1 : rootChar c (w • g2a) = c g2ia ^ (3 - k) * c g2ir ^ (3 : ℤ) := by
    rw [hw1, rootChar_add, rootChar_zsmul, rootChar_zsmul, rootChar_g2a, rootChar_g2r]
  have e2 : rootChar c (w • g2r) = (c g2ia)⁻¹ * c g2ir ^ (-k) := by
    rw [hw2, rootChar_add, rootChar_zsmul, rootChar_zsmul, rootChar_g2a, rootChar_g2r,
      zpow_neg_one]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← e1, h, rootChar_g2a, zpow_natCast]
    · rw [← e2, h, rootChar_g2r, zpow_natCast]
  · rintro ⟨h1, h2⟩ v
    conv_lhs => rw [g2_eq_smul_add v]
    conv_rhs => rw [g2_eq_smul_add v]
    rw [smul_add, smul_comm w (v g2ia), smul_comm w (v g2ir), rootChar_add, rootChar_zsmul,
      rootChar_zsmul, e1, e2, h1, h2, rootChar_add, rootChar_zsmul, rootChar_zsmul, rootChar_g2a,
      rootChar_g2r, mul_pow, zpow_natCast_zpow_comm, zpow_natCast_zpow_comm]

theorem smul_ne_of_G2_rot {w : WeylGroup .G2} {k : ℤ} (hk : k = 1 ∨ k = 2)
    (hw1 : w • g2a = (3 - k) • g2a + (3 : ℤ) • g2r)
    (hw2 : w • g2r = (-1 : ℤ) • g2a + (-k) • g2r) {α : Fin Tag.G2.rank → ℤ}
    (hα : IsRoot .G2 α) : w • α ≠ α ∧ w • α ≠ -α := by
  have hv : w • α = α g2ia • ((3 - k) • g2a + (3 : ℤ) • g2r) +
      α g2ir • ((-1 : ℤ) • g2a + (-k) • g2r) := by
    conv_lhs => rw [g2_eq_smul_add α]
    rw [smul_add, smul_comm w (α g2ia), smul_comm w (α g2ir), hw1, hw2]
  have hia : (w • α) g2ia = α g2ia * (3 - k) - α g2ir := by
    rw [hv]
    simp [g2a_ia, g2r_ia]
    ring
  have hir : (w • α) g2ir = 3 * α g2ia - k * α g2ir := by
    rw [hv]
    simp [g2a_ir, g2r_ir]
    ring
  have h0 : α g2ia = 0 → α g2ir = 0 → False := fun h0 h1 => hα.ne_zero (funext fun j => by
    rcases fin_G2_cases j with rfl | rfl
    · exact h0
    · exact h1)
  constructor
  · intro h
    have e0 : α g2ia * (3 - k) - α g2ir = α g2ia := by rw [← hia, h]
    have e1 : 3 * α g2ia - k * α g2ir = α g2ir := by rw [← hir, h]
    rcases hk with rfl | rfl <;> exact h0 (by linarith) (by linarith)
  · intro h
    have e0 : α g2ia * (3 - k) - α g2ir = -α g2ia := by rw [← hia, h, Pi.neg_apply]
    have e1 : 3 * α g2ia - k * α g2ir = -α g2ir := by rw [← hir, h, Pi.neg_apply]
    rcases hk with rfl | rfl <;> exact h0 (by linarith) (by linarith)

theorem g2rot_one_g2a :
    (simple .G2 g2ia * simple .G2 g2ir) • g2a = (3 - 1 : ℤ) • g2a + (3 : ℤ) • g2r := by
  rw [mul_smul, simple_smul, simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem g2rot_one_g2r :
    (simple .G2 g2ia * simple .G2 g2ir) • g2r = (-1 : ℤ) • g2a + (-1 : ℤ) • g2r := by
  rw [mul_smul, simple_smul, simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem g2rot_two_g2a :
    (simple .G2 g2ia * simple .G2 g2ir * (simple .G2 g2ia * simple .G2 g2ir)) • g2a =
      (3 - 2 : ℤ) • g2a + (3 : ℤ) • g2r := by
  simp only [mul_smul, simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem g2rot_two_g2r :
    (simple .G2 g2ia * simple .G2 g2ir * (simple .G2 g2ia * simple .G2 g2ir)) • g2r =
      (-1 : ℤ) • g2a + (-2 : ℤ) • g2r := by
  simp only [mul_smul, simple_smul]
  exact List.ofFn_injective (by decide +kernel)

@[expose] def torusTupleHom (m : ℤ) : Lˣ →* (Fin Tag.G2.rank → Lˣ) where
  toFun ζ i := if i = g2ia then ζ ^ m else ζ
  map_one' := by
    funext i
    by_cases hi : i = g2ia <;> simp [hi]
  map_mul' ζ η := by
    funext i
    by_cases hi : i = g2ia <;> simp [hi, mul_zpow]

theorem torusTupleHom_ia (m : ℤ) (ζ : Lˣ) : torusTupleHom m ζ g2ia = ζ ^ m := by
  simp [torusTupleHom]

theorem torusTupleHom_ir (m : ℤ) (ζ : Lˣ) : torusTupleHom m ζ g2ir = ζ := by
  simp [torusTupleHom, g2ia, g2ir]

theorem eq_torusTupleHom_iff (m : ℤ) (c : Fin Tag.G2.rank → Lˣ) :
    c = torusTupleHom m (c g2ir) ↔ c g2ia = c g2ir ^ m := by
  constructor
  · intro h
    conv_lhs => rw [h]
    exact torusTupleHom_ia m _
  · intro h
    funext j
    rcases fin_G2_cases j with rfl | rfl
    · rw [torusTupleHom_ia, h]
    · rw [torusTupleHom_ir]

@[expose] def cyclicTorus (m : ℤ) (d : ℕ) : Subgroup (ModGL .G2 L) :=
  (rootsOfUnity d L).map ((rootDiagUnitHom .G2 L).comp (torusTupleHom m))

theorem injective_torus_map (m : ℤ) :
    Function.Injective ((rootDiagUnitHom .G2 L).comp (torusTupleHom (L := L) m)) := by
  intro ζ η h
  have h' := rootDiagUnit_injective h
  have := congrFun h' g2ir
  simpa [torusTupleHom_ir] using this

theorem rootDiagUnit_mem_cyclicTorus_iff (m : ℤ) (d : ℕ) (c : Fin Tag.G2.rank → Lˣ) :
    rootDiagUnit .G2 c ∈ cyclicTorus m d ↔ c g2ia = c g2ir ^ m ∧ c g2ir ^ d = 1 := by
  constructor
  · rintro ⟨ζ, hζ, h⟩
    have hc : torusTupleHom m ζ = c := rootDiagUnit_injective h
    rw [← hc, torusTupleHom_ia, torusTupleHom_ir]
    exact ⟨rfl, (mem_rootsOfUnity d ζ).1 hζ⟩
  · rintro ⟨h1, h2⟩
    refine ⟨c g2ir, (mem_rootsOfUnity d _).2 h2, ?_⟩
    change rootDiagUnit .G2 (torusTupleHom m (c g2ir)) = rootDiagUnit .G2 c
    rw [← (eq_torusTupleHom_iff m c).2 h1]

theorem cyclicTorus_le_torusGroup (m : ℤ) (d : ℕ) :
    cyclicTorus (L := L) m d ≤ torusGroup .G2 L := by
  obtain ⟨⟨B, hB, -⟩, hdiag⟩ := G2_F4_root_character_diagonals_inner .G2 (Or.inl rfl) L
  rintro _ ⟨ζ, -, rfl⟩
  exact (hdiag B hB _).2.1

theorem torusGroup_le_adjointGroup_G2 {M : Type} [Field M] :
    torusGroup .G2 M ≤ adjointGroup .G2 M := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, t⟩, rfl⟩
  exact torusElt_mem_adjointGroup i t

theorem map_conj_centralizer_singleton_eq {G : Type*} [Group G] (g x : G) :
    (Subgroup.centralizer {x}).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer {g * x * g⁻¹} := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    calc g * z * g⁻¹ * (g * x * g⁻¹) = g * (z * x) * g⁻¹ := by group
      _ = g * (x * z) * g⁻¹ := by rw [hz]
      _ = g * x * g⁻¹ * (g * z * g⁻¹) := by group
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, by group⟩
    calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [hy]
      _ = x * (g⁻¹ * y * g) := by group

theorem centralizer_le_comap_conj {L : Type} [Field L] {C : Type*} [Group C]
    (ι : C →* ModGL .G2 L) (F : L →+* L) {n g : ModGL .G2 L} (hgG : g ∈ adjointGroup .G2 L)
    (hFg : Units.map (entrywiseHom F) g = g * n)
    (hrange : ι.range = adjointGroup .G2 L ⊓ (Units.map (entrywiseHom F)).eqLocus
      (MonoidHom.id _))
    {T₀ : Subgroup (ModGL .G2 L)}
    (hchar : ∀ u ∈ torusGroup .G2 L, (n * Units.map (entrywiseHom F) u * n⁻¹ = u ↔ u ∈ T₀))
    {t : C} {c : Fin Tag.G2.rank → Lˣ} (hct : g * rootDiagUnit .G2 c * g⁻¹ = ι t)
    (hX : toralCentralizer .G2 L c = torusGroup .G2 L) :
    Subgroup.centralizer {t} ≤ (T₀.map (MulAut.conj g).toMonoidHom).comap ι := by
  intro y hy
  have hyt : t * y = y * t := Subgroup.mem_centralizer_iff.1 hy t rfl
  have hyF : ι y ∈ ι.range := ⟨y, rfl⟩
  rw [hrange] at hyF
  obtain ⟨hyG, hyFix⟩ := Subgroup.mem_inf.1 hyF
  have hyFix' : Units.map (entrywiseHom F) (ι y) = ι y := hyFix
  obtain ⟨u, hu⟩ : ∃ u, u = g⁻¹ * ι y * g := ⟨_, rfl⟩
  have huG : u ∈ adjointGroup .G2 L := hu ▸ mul_mem (mul_mem (inv_mem hgG) hyG) hgG
  have hdc : rootDiagUnit .G2 c = g⁻¹ * ι t * g := by
    rw [← hct]
    group
  have huc : u ∈ Subgroup.centralizer {rootDiagUnit .G2 c} := by
    rw [Subgroup.mem_centralizer_singleton_iff, hdc, hu]
    have hιyt : ι t * ι y = ι y * ι t := by rw [← map_mul, hyt, map_mul]
    calc g⁻¹ * ι y * g * (g⁻¹ * ι t * g) = g⁻¹ * (ι y * ι t) * g := by group
      _ = g⁻¹ * (ι t * ι y) * g := by rw [hιyt]
      _ = g⁻¹ * ι t * g * (g⁻¹ * ι y * g) := by group
  have huH : u ∈ torusGroup .G2 L := by
    rw [← hX]
    exact Subgroup.mem_inf.2 ⟨huG, huc⟩
  have h2 : g * u * g⁻¹ = ι y := by
    rw [hu]
    group
  have hufix : n * Units.map (entrywiseHom F) u * n⁻¹ = u := by
    have h1 : Units.map (entrywiseHom F) (g * u * g⁻¹) =
        g * (n * Units.map (entrywiseHom F) u * n⁻¹) * g⁻¹ := by
      rw [map_mul, map_mul, map_inv, hFg]
      group
    rw [h2, hyFix', ← h2] at h1
    simpa using h1.symm
  exact ⟨u, (hchar u huH).1 hufix, by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact h2⟩

theorem cyclotomic_core (K : Type) [Field K] [Finite K] {k : ℤ} (hk : k = 1 ∨ k = 2)
    {w : WeylGroup .G2} (hw1 : w • g2a = (3 - k) • g2a + (3 : ℤ) • g2r)
    (hw2 : w • g2r = (-1 : ℤ) • g2a + (-k) • g2r) (d : ℕ)
    (hd : (d : ℤ) = (Nat.card K : ℤ) ^ 2 + (2 * k - 3) * Nat.card K + 1) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) :
    ∃ T : Subgroup (adjointGroup .G2 K), IsCyclic T ∧ Nat.card T = d ∧
      ∀ t ∈ T, orderOf t = p → Subgroup.centralizer {t} = T := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set q := Nat.card K with hq
  have hℓ : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  obtain ⟨e, -, hqe⟩ := FiniteField.card K (ringChar K)
  let L := AlgebraicClosure K
  have : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  have : ExpChar L (ringChar K) := ExpChar.prime hℓ
  set F : L →+* L := iterateFrobenius L (ringChar K) e
  have hF : ∀ c : L, F c = c ^ q := fun c => by
    rw [iterateFrobenius_def, hq, Nat.card_eq_fintype_card, hqe]
  have hFbij : Function.Bijective F := frobenius_bijective (k := K) F hF
  obtain ⟨S, hS, hLang⟩ :=
    (exceptional_all_characteristic_field_Lang_surjectivity (ringChar K) L (e : ℕ) e.pos).1 .G2
  obtain ⟨n, hn, hnG⟩ : ∃ n, n = canonicalRep (coxeterSystem .G2) L w ∧
      n ∈ adjointGroup .G2 L := ⟨_, rfl, canonicalRep_mem_adjointGroup _ L w⟩
  obtain ⟨g₀, hg₀⟩ := hLang ⟨n, hnG⟩
  set g : ModGL .G2 L := (g₀ : ModGL .G2 L) with hgdef
  have hFg : Units.map (entrywiseHom F) g = g * n := by
    have h := congrArg Subtype.val hg₀
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    rw [hS] at h
    rw [h, mul_inv_cancel_left]
  have hgG : g ∈ adjointGroup .G2 L := g₀.2
  set m : ℤ := -((q : ℤ) + k) with hm
  set T₀ := cyclicTorus (L := L) m d with hT₀
  have hT₀H : T₀ ≤ torusGroup .G2 L := cyclicTorus_le_torusGroup m d
  have hHG : torusGroup .G2 L ≤ adjointGroup .G2 L := torusGroup_le_adjointGroup_G2
  have hHcomm := (triangular_borel_structure.{0, 0} .G2 L).1
  have hchar : ∀ u ∈ torusGroup .G2 L,
      (n * Units.map (entrywiseHom F) u * n⁻¹ = u ↔ u ∈ T₀) := by
    intro u hu
    obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hu
    rw [hn, conj_frob_rootDiagUnit_eq_iff F hF w c, forall_rootChar_iff_G2 hw1 hw2,
      T0_equations_iff (q : ℤ) k hk, rootDiagUnit_mem_cyclicTorus_iff, ← hd, zpow_natCast]
  have hqK : ((q : ℕ) : K) = 0 := by
    rw [hq, Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero K
  have hdK : (d : K) = 1 := by
    have h := congrArg (Int.cast : ℤ → K) hd
    push_cast at h
    rw [h, hqK]
    ring
  have : NeZero (d : K) := ⟨by rw [hdK]; exact one_ne_zero⟩
  have : NeZero d := ⟨fun h0 => by simp [h0] at hdK⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := L) (n := d)
  have hcardT₀ : Nat.card T₀ = d := by
    rw [hT₀, cyclicTorus, Subgroup.card_map_of_injective (injective_torus_map m),
      hζ.card_rootsOfUnity]
  have hcycT₀ : IsCyclic T₀ :=
    isCyclic_of_surjective _
      (((rootDiagUnitHom .G2 L).comp (torusTupleHom m)).subgroupMap_surjective (rootsOfUnity d L))
  set Tc := T₀.map (MulAut.conj g).toMonoidHom with hTc
  obtain ⟨ι, hι⟩ : ∃ ι : adjointGroup .G2 K →* ModGL .G2 L,
      ι = (baseChangeGL (algebraMap K L)).comp (adjointGroup .G2 K).subtype := ⟨_, rfl⟩
  have hιinj : Function.Injective ι := by
    rw [hι]
    exact (baseChangeGL_injective (τ := .G2) (algebraMap K L)).comp Subtype.val_injective
  have hrange : ι.range = adjointGroup .G2 L ⊓ (Units.map (entrywiseHom F)).eqLocus
      (MonoidHom.id _) := by
    rw [hι, MonoidHom.range_comp, Subgroup.range_subtype,
      frobenius_fixed_eq_map_of_bijective (Or.inl rfl) F hF hFbij]
  have hconjF : ∀ u : ModGL .G2 L, Units.map (entrywiseHom F) (g * u * g⁻¹) =
      g * (n * Units.map (entrywiseHom F) u * n⁻¹) * g⁻¹ := fun u => by
    rw [map_mul, map_mul, map_inv, hFg]
    group
  have hTcι : Tc ≤ ι.range := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hrange]
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hgG (hHG (hT₀H hu))) (inv_mem hgG), ?_⟩
    change Units.map (entrywiseHom F) (g * u * g⁻¹) = g * u * g⁻¹
    rw [hconjF, (hchar u (hT₀H hu)).2 hu]
  set T := Tc.comap ι with hT
  have eT : T ≃* T₀ :=
    ((Subgroup.equivMapOfInjective T ι hιinj).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hTcι))).trans
      (Subgroup.equivMapOfInjective T₀ (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).symm
  have hcardT : Nat.card T = d := by rw [Nat.card_congr eT.toEquiv, hcardT₀]
  have hcycT : IsCyclic T := isCyclic_of_injective eT.toMonoidHom eT.injective
  have hTcomm : ∀ y ∈ T, ∀ z ∈ T, y * z = z * y := by
    intro y hy z hz
    apply hιinj
    obtain ⟨u, hu, hyu⟩ := hy
    obtain ⟨u', hu', hzu⟩ := hz
    rw [map_mul, map_mul, ← hyu, ← hzu]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hc := hHcomm u (hT₀H hu) u' (hT₀H hu')
    calc g * u * g⁻¹ * (g * u' * g⁻¹) = g * (u * u') * g⁻¹ := by group
      _ = g * (u' * u) * g⁻¹ := by rw [hc]
      _ = g * u' * g⁻¹ * (g * u * g⁻¹) := by group
  refine ⟨T, hcycT, hcardT, fun t ht hto => ?_⟩
  have ht' := ht
  obtain ⟨h, hh, hht⟩ := ht
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hT₀H hh)
  have hoc : orderOf c = p := by
    rw [← orderOf_rootDiagUnit (K := L) (τ := .G2) c,
      ← orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
        (rootDiagUnit .G2 c), hht,
      orderOf_injective ι hιinj t, hto]
  have hcp : c ^ p = 1 := hoc ▸ pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hoc
    exact hp.one_lt.ne hoc
  have hfix : ∀ v, rootChar c (w • v) = rootChar c v ^ q :=
    (conj_frob_rootDiagUnit_eq_iff F hF w c).1 (hn ▸ (hchar _ (hT₀H hh)).2 hh)
  have hker : rootCharKernel c = ∅ := by
    rcases rootCharKernel_G2_cases hp hp3 hcp hc1 with h0 | ⟨α, hα, hkerα⟩
    · exact h0
    · exfalso
      have hαK : α ∈ rootCharKernel c := by rw [hkerα]; exact Or.inl rfl
      have hwα : w • α ∈ rootCharKernel c :=
        ⟨IsRoot.smul hαK.1 w, by rw [hfix, hαK.2, one_pow]⟩
      rw [hkerα] at hwα
      rcases hwα with h1 | h1
      · exact (smul_ne_of_G2_rot hk hw1 hw2 hα).1 h1
      · exact (smul_ne_of_G2_rot hk hw1 hw2 hα).2 h1
  have hX : toralCentralizer .G2 L c = torusGroup .G2 L := by
    rw [toralCentralizer_eq_toralRootGroup_of_le
      (rootCharStabilizer_le_kernelReflectionGroup_G2 hp hp3 hcp hc1), toralRootGroup, hker]
    simp [rootSpan]
  refine le_antisymm (centralizer_le_comap_conj ι F hgG hFg hrange hchar hht hX) fun y hy => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  exact hTcomm z ht' y hy

theorem not_dvd_index_of_card_eq (K : Type) [Field K] [Finite K] {k : ℤ} (hk : k = 1 ∨ k = 2)
    (d : ℕ) (hd : (d : ℤ) = (Nat.card K : ℤ) ^ 2 + (2 * k - 3) * Nat.card K + 1) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpd : p ∣ d) (T : Subgroup (adjointGroup .G2 K))
    (hT : Nat.card T = d) : ¬ p ∣ T.index := by
  have : Fact p.Prime := ⟨hp⟩
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hcard := T.card_mul_index
  rw [hT, card_adjointGroup_G2, CFSG.Open.ordG2] at hcard
  have hcardZ : (d : ℤ) * T.index =
      (Nat.card K : ℤ) ^ 6 * ((Nat.card K : ℤ) ^ 6 - 1) * ((Nat.card K : ℤ) ^ 2 - 1) := by
    have h6 : 1 ≤ Nat.card K ^ 6 := Nat.one_le_pow _ _ hq1
    have h2 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ hq1
    have h := congrArg (Nat.cast : ℕ → ℤ) hcard
    push_cast [Nat.cast_sub h6, Nat.cast_sub h2] at h
    exact h
  have hd0 : (d : ℤ) ≠ 0 := by
    have hpos : (0 : ℤ) < (Nat.card K : ℤ) ^ 2 + (2 * k - 3) * Nat.card K + 1 := by
      rcases hk with rfl | rfl <;> nlinarith
    rw [hd]
    exact hpos.ne'
  have hidx : (T.index : ℤ) = (Nat.card K : ℤ) ^ 6 * ((Nat.card K : ℤ) ^ 2 - 1) ^ 2 *
      ((Nat.card K : ℤ) ^ 2 - (2 * k - 3) * Nat.card K + 1) := by
    apply mul_left_cancel₀ hd0
    rw [hcardZ, hd]
    rcases hk with rfl | rfl <;> ring
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = (Nat.card K : ℤ) := ⟨_, rfl⟩
  have hpd' : (p : ℤ) ∣ Q ^ 2 + (2 * k - 3) * Q + 1 := by
    rw [hQ, ← hd]
    exact_mod_cast hpd
  intro hdvd
  have hpi : (p : ℤ) ∣ Q ^ 6 * (Q ^ 2 - 1) ^ 2 * (Q ^ 2 - (2 * k - 3) * Q + 1) := by
    rw [hQ, ← hidx]
    exact_mod_cast hdvd
  have hp1 : ¬ (p : ℤ) ∣ 1 := hpZ.not_dvd_one
  have hp2 : ¬ (p : ℤ) ∣ 2 := fun h => by
    have := Int.le_of_dvd (by norm_num) h
    omega
  have hp3' : ¬ (p : ℤ) ∣ 3 := fun h => by
    have := Int.le_of_dvd (by norm_num) h
    omega
  have hq : ¬ (p : ℤ) ∣ Q := fun h => hp1 (by
    have h' := dvd_sub hpd' (dvd_mul_of_dvd_left h (Q + (2 * k - 3)))
    rwa [show Q ^ 2 + (2 * k - 3) * Q + 1 - Q * (Q + (2 * k - 3)) = 1 by ring] at h')
  rcases hpZ.dvd_or_dvd hpi with h | h
  · rcases hpZ.dvd_or_dvd h with h | h
    · exact hq (hpZ.dvd_of_dvd_pow h)
    · have h1 := hpZ.dvd_of_dvd_pow h
      have h2 : (p : ℤ) ∣ (2 * k - 3) * Q + 2 := by
        have h' := dvd_sub hpd' h1
        rwa [show Q ^ 2 + (2 * k - 3) * Q + 1 - (Q ^ 2 - 1) = (2 * k - 3) * Q + 2 by ring] at h'
      have h3 := dvd_sub h1 (dvd_mul_of_dvd_left h2 ((2 * k - 3) * Q - 2))
      rw [show Q ^ 2 - 1 - ((2 * k - 3) * Q + 2) * ((2 * k - 3) * Q - 2) = 3 by
        rcases hk with rfl | rfl <;> ring] at h3
      exact hp3' h3
  · have h2q : (p : ℤ) ∣ 2 * ((2 * k - 3) * Q) := by
      have h' := dvd_sub hpd' h
      rwa [show Q ^ 2 + (2 * k - 3) * Q + 1 - (Q ^ 2 - (2 * k - 3) * Q + 1) =
        2 * ((2 * k - 3) * Q) by ring] at h'
    rcases hpZ.dvd_or_dvd h2q with h | h
    · exact hp2 h
    · rcases hpZ.dvd_or_dvd h with h | h
      · rcases hk with rfl | rfl
        · exact hp1 (dvd_neg.1 (by simpa using h))
        · exact hp1 (by simpa using h)
      · exact hq h

theorem odd_G2_cyclotomic_three_six_tori_and_prime_centralizers (K : Type) [Field K] [Finite K]
    (hK : Odd (Nat.card K)) (ε : ℤ) (hε : ε = -1 ∨ ε = 1) (d : ℕ)
    (hd : (d : ℤ) = (Nat.card K : ℤ) ^ 2 + ε * Nat.card K + 1) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpd : p ∣ d) :
    ∃ T : Subgroup (adjointGroup .G2 K), IsCyclic T ∧ Nat.card T = d ∧
      (∃ S : Sylow p (adjointGroup .G2 K), (S : Subgroup (adjointGroup .G2 K)) ≤ T) ∧
      (∀ P : Subgroup (adjointGroup .G2 K), IsPGroup p P → IsCyclic P) ∧
      ∀ x : adjointGroup .G2 K, orderOf x = p →
        (∃ g : adjointGroup .G2 K, g * x * g⁻¹ ∈ T) ∧
        (∃ g : adjointGroup .G2 K,
          (Subgroup.centralizer {x}).map (MulAut.conj g).toMonoidHom = T) ∧
        IsCyclic (Subgroup.centralizer ({x} : Set (adjointGroup .G2 K))) ∧
        Nat.card (Subgroup.centralizer ({x} : Set (adjointGroup .G2 K))) = d ∧ Odd d := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (Module.End K (RootModule .G2 K)) := Module.finite_of_finite K
  obtain ⟨T, hcyc, hcard, hcent, hidx⟩ : ∃ T : Subgroup (adjointGroup .G2 K), IsCyclic T ∧
      Nat.card T = d ∧ (∀ t ∈ T, orderOf t = p → Subgroup.centralizer {t} = T) ∧
      ¬ p ∣ T.index := by
    rcases hε with rfl | rfl
    · obtain ⟨T, h1, h2, h3⟩ := cyclotomic_core K (Or.inl rfl) g2rot_one_g2a g2rot_one_g2r d
        (by rw [hd]; ring) hp hp3
      exact ⟨T, h1, h2, h3,
        not_dvd_index_of_card_eq K (Or.inl rfl) d (by rw [hd]; ring) hp hp3 hpd T h2⟩
    · obtain ⟨T, h1, h2, h3⟩ := cyclotomic_core K (Or.inr rfl) g2rot_two_g2a g2rot_two_g2r d
        (by rw [hd]; ring) hp hp3
      exact ⟨T, h1, h2, h3,
        not_dvd_index_of_card_eq K (Or.inr rfl) d (by rw [hd]; ring) hp hp3 hpd T h2⟩
  have hdodd : Odd d := by
    obtain ⟨j, hj⟩ := hK
    rcases hε with rfl | rfl
    · refine ⟨2 * j ^ 2 + j, ?_⟩
      zify
      rw [hd, hj]
      push_cast
      ring
    · refine ⟨2 * j ^ 2 + 3 * j + 1, ?_⟩
      zify
      rw [hd, hj]
      push_cast
      ring
  have hconjT : ∀ P : Subgroup (adjointGroup .G2 K), IsPGroup p P →
      ∃ g : adjointGroup .G2 K, P.map (MulAut.conj g).toMonoidHom ≤ T := fun P hP =>
    exists_conj_map_le_of_not_dvd_index hidx hP
  refine ⟨T, hcyc, hcard, ?_, fun P hP => ?_, fun x hx => ?_⟩
  · obtain ⟨S₀⟩ : Nonempty (Sylow p T) := inferInstance
    have hS : IsPGroup p ((S₀ : Subgroup T).map T.subtype) := S₀.isPGroup'.map T.subtype
    have hSi : ¬ p ∣ ((S₀ : Subgroup T).map T.subtype).index := by
      rw [Subgroup.index_map_subtype]
      exact fun h => ((Fact.out : p.Prime).dvd_mul.1 h).elim S₀.not_dvd_index hidx
    exact ⟨hS.toSylow hSi, by
      rw [IsPGroup.toSylow_coe]
      exact Subgroup.map_subtype_le _⟩
  · obtain ⟨g, hg⟩ := hconjT P hP
    exact isCyclic_of_injective
      (MonoidHom.codRestrict ((MulAut.conj g).toMonoidHom.comp P.subtype) T
        fun y => hg ⟨y, y.2, rfl⟩)
      fun y z h => Subtype.ext ((MulAut.conj g).injective (congrArg Subtype.val h))
  · have hPx : IsPGroup p (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
    obtain ⟨g, hg⟩ := hconjT _ hPx
    have hxT : g * x * g⁻¹ ∈ T := hg ⟨x, Subgroup.mem_zpowers x, rfl⟩
    have hto : orderOf (g * x * g⁻¹) = p := by
      rw [← MulAut.conj_apply, ← MulEquiv.coe_toMonoidHom,
        orderOf_injective _ (MulAut.conj g).injective x, hx]
    have hmap : (Subgroup.centralizer {x}).map (MulAut.conj g).toMonoidHom = T := by
      rw [map_conj_centralizer_singleton_eq, hcent _ hxT hto]
    have e : Subgroup.centralizer ({x} : Set (adjointGroup .G2 K)) ≃* T :=
      (Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).trans
        (MulEquiv.subgroupCongr hmap)
    exact ⟨⟨g, hxT⟩, ⟨g, hmap⟩, isCyclic_of_injective e.toMonoidHom e.injective,
      by rw [Nat.card_congr e.toEquiv, hcard], hdodd⟩

end CFSG.RankThree.Chevalley
