module

public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex
public import CFSG.RankThree.Chevalley.SteinbergCAF4CyclotomicTorus
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusTorus

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.E6 F4Weyl
  CFSG.LieType.AlgebraicGroups EvenF4QPlus

theorem zpow_pair_iff {M : Type*} [CommGroup M] (x : M) (q ε : ℤ) :
    (x ^ q) ^ q = (x ^ q) ^ ε * x⁻¹ ↔ x ^ (q ^ 2 - ε * q + 1) = 1 := by
  rw [← zpow_mul, ← zpow_mul, ← zpow_neg_one, ← zpow_add, ← mul_inv_eq_one, ← zpow_neg,
    ← zpow_add]
  ring_nf

structure F4PairBasis (w : WeylGroup .F4) where
  B : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ
  N : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ
  ε : ℤ
  smul_zero : w • f4Col B (f4Index 0) = f4Col B (f4Index 1)
  smul_one : w • f4Col B (f4Index 1) = ε • f4Col B (f4Index 1) - f4Col B (f4Index 0)
  smul_two : w • f4Col B (f4Index 2) = f4Col B (f4Index 3)
  smul_three : w • f4Col B (f4Index 3) = ε • f4Col B (f4Index 3) - f4Col B (f4Index 2)
  N_mul : N * B = 1
  mul_N : B * N = 1

namespace F4PairBasis

variable {w : WeylGroup .F4} (D : F4PairBasis w) {L : Type} [Field L]

theorem single_eq_sum (j : Fin Tag.F4.rank) :
    (Pi.single j 1 : Fin Tag.F4.rank → ℤ) = ∑ i, D.N i j • f4Col D.B i := by
  funext t
  have h := congrFun (congrFun D.mul_N t) j
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, f4Col]
  rw [Pi.single_apply, ← h]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem eq_of_rootChar_basis {c c' : Fin Tag.F4.rank → Lˣ}
    (h : ∀ k, rootChar c (f4Col D.B k) = rootChar c' (f4Col D.B k)) : c = c' := by
  funext j
  have e : ∀ a : Fin Tag.F4.rank → Lˣ, a j = ∏ i, rootChar a (f4Col D.B i) ^ D.N i j := by
    intro a
    rw [← rootChar_pi_single a j, D.single_eq_sum j, rootChar_sum]
    exact Finset.prod_congr rfl fun i _ => rootChar_zsmul a _ _
  rw [e c, e c']
  exact Finset.prod_congr rfl fun i _ => by rw [h i]

@[expose] def pairTuple (q : ℕ) (ζ η : Lˣ) : Fin Tag.F4.rank → Lˣ :=
  fun j => ζ ^ (D.N (f4Index 0) j + (q : ℤ) * D.N (f4Index 1) j) *
    η ^ (D.N (f4Index 2) j + (q : ℤ) * D.N (f4Index 3) j)

@[expose] def pairTupleHom (q : ℕ) : Lˣ × Lˣ →* (Fin Tag.F4.rank → Lˣ) where
  toFun x := D.pairTuple q x.1 x.2
  map_one' := by
    funext j
    simp [pairTuple]
  map_mul' x y := by
    funext j
    simp only [pairTuple, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, mul_zpow]
    exact mul_mul_mul_comm _ _ _ _

theorem pairTupleHom_apply (q : ℕ) (x : Lˣ × Lˣ) :
    D.pairTupleHom q x = D.pairTuple q x.1 x.2 :=
  rfl

theorem one_apply_f4Index (i j : Fin 4) :
    (1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) (f4Index i) (f4Index j) =
      if i = j then 1 else 0 := by
  rw [Matrix.one_apply]
  rfl

theorem rootChar_pairTuple_col (q : ℕ) (ζ η : Lˣ) (k : Fin Tag.F4.rank) :
    rootChar (D.pairTuple q ζ η) (f4Col D.B k) =
      ζ ^ ((1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) (f4Index 0) k +
          (q : ℤ) * (1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) (f4Index 1) k) *
        η ^ ((1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) (f4Index 2) k +
          (q : ℤ) * (1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) (f4Index 3) k) := by
  rw [← D.N_mul, rootChar]
  simp only [pairTuple, f4Col, mul_zpow, ← zpow_mul, Finset.prod_mul_distrib,
    prod_zpow_eq_zpow_sum, Matrix.mul_apply]
  congr 2
  · rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  · rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem rootChar_pairTuple_zero (q : ℕ) (ζ η : Lˣ) :
    rootChar (D.pairTuple q ζ η) (f4Col D.B (f4Index 0)) = ζ := by
  rw [rootChar_pairTuple_col]
  simp [one_apply_f4Index]

theorem rootChar_pairTuple_one (q : ℕ) (ζ η : Lˣ) :
    rootChar (D.pairTuple q ζ η) (f4Col D.B (f4Index 1)) = ζ ^ (q : ℤ) := by
  rw [rootChar_pairTuple_col]
  simp [one_apply_f4Index]

theorem rootChar_pairTuple_two (q : ℕ) (ζ η : Lˣ) :
    rootChar (D.pairTuple q ζ η) (f4Col D.B (f4Index 2)) = η := by
  rw [rootChar_pairTuple_col]
  simp [one_apply_f4Index]

theorem rootChar_pairTuple_three (q : ℕ) (ζ η : Lˣ) :
    rootChar (D.pairTuple q ζ η) (f4Col D.B (f4Index 3)) = η ^ (q : ℤ) := by
  rw [rootChar_pairTuple_col]
  simp [one_apply_f4Index]

theorem pairTupleHom_injective (q : ℕ) : Function.Injective (D.pairTupleHom (L := L) q) := by
  rintro ⟨ζ, η⟩ ⟨ζ', η'⟩ h
  have h0 := congrArg (fun c => rootChar c (f4Col D.B (f4Index 0))) h
  have h2 := congrArg (fun c => rootChar c (f4Col D.B (f4Index 2))) h
  simp only [pairTupleHom_apply, rootChar_pairTuple_zero, rootChar_pairTuple_two] at h0 h2
  rw [h0, h2]

theorem forall_rootChar_smul_eq_pow_iff (q : ℕ) (c : Fin Tag.F4.rank → Lˣ) :
    (∀ v, rootChar c (w • v) = rootChar c v ^ q) ↔
      ∃ ζ η : Lˣ, ζ ^ ((q : ℤ) ^ 2 - D.ε * q + 1) = 1 ∧ η ^ ((q : ℤ) ^ 2 - D.ε * q + 1) = 1 ∧
        c = D.pairTuple q ζ η := by
  constructor
  · intro h
    obtain ⟨ζ, hζ⟩ : ∃ ζ, ζ = rootChar c (f4Col D.B (f4Index 0)) := ⟨_, rfl⟩
    obtain ⟨η, hη⟩ : ∃ η, η = rootChar c (f4Col D.B (f4Index 2)) := ⟨_, rfl⟩
    have h1 : rootChar c (f4Col D.B (f4Index 1)) = ζ ^ (q : ℤ) := by
      rw [← D.smul_zero, h, hζ, zpow_natCast]
    have h3 : rootChar c (f4Col D.B (f4Index 3)) = η ^ (q : ℤ) := by
      rw [← D.smul_two, h, hη, zpow_natCast]
    have h1' := h (f4Col D.B (f4Index 1))
    rw [D.smul_one, sub_eq_add_neg, rootChar_add, rootChar_neg_eq_inv, rootChar_zsmul, h1,
      ← hζ, ← zpow_natCast] at h1'
    have h3' := h (f4Col D.B (f4Index 3))
    rw [D.smul_three, sub_eq_add_neg, rootChar_add, rootChar_neg_eq_inv, rootChar_zsmul, h3,
      ← hη, ← zpow_natCast] at h3'
    refine ⟨ζ, η, (zpow_pair_iff ζ q D.ε).1 h1'.symm, (zpow_pair_iff η q D.ε).1 h3'.symm,
      D.eq_of_rootChar_basis fun k => ?_⟩
    fin_cases k
    · show rootChar c (f4Col D.B (f4Index 0)) = rootChar (D.pairTuple q ζ η) (f4Col D.B (f4Index 0))
      rw [D.rootChar_pairTuple_zero, hζ]
    · show rootChar c (f4Col D.B (f4Index 1)) = rootChar (D.pairTuple q ζ η) (f4Col D.B (f4Index 1))
      rw [D.rootChar_pairTuple_one, h1]
    · show rootChar c (f4Col D.B (f4Index 2)) = rootChar (D.pairTuple q ζ η) (f4Col D.B (f4Index 2))
      rw [D.rootChar_pairTuple_two, hη]
    · show rootChar c (f4Col D.B (f4Index 3)) = rootChar (D.pairTuple q ζ η) (f4Col D.B (f4Index 3))
      rw [D.rootChar_pairTuple_three, h3]
  · rintro ⟨ζ, η, hζ, hη, rfl⟩ v
    have hsmul : ∀ (c : Fin Tag.F4.rank → Lˣ) (x : Fin Tag.F4.rank → ℤ),
        rootChar c (w • x) = rootChar (fun j => rootChar c (w • Pi.single j 1)) x := by
      intro c x
      rw [smul_eq_sum_smul_single w x, rootChar_sum, rootChar]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [rootChar_zsmul]
    have hc : (fun j => rootChar (D.pairTuple q ζ η) (w • Pi.single j 1)) =
        D.pairTuple q ζ η ^ q := by
      refine D.eq_of_rootChar_basis fun k => ?_
      rw [← hsmul, rootChar_pow_tuple]
      fin_cases k
      · show rootChar (D.pairTuple q ζ η) (w • f4Col D.B (f4Index 0)) =
          rootChar (D.pairTuple q ζ η) (f4Col D.B (f4Index 0)) ^ q
        rw [D.smul_zero, D.rootChar_pairTuple_one, D.rootChar_pairTuple_zero, zpow_natCast]
      · show rootChar (D.pairTuple q ζ η) (w • f4Col D.B (f4Index 1)) =
          rootChar (D.pairTuple q ζ η) (f4Col D.B (f4Index 1)) ^ q
        rw [D.smul_one, sub_eq_add_neg, rootChar_add, rootChar_neg_eq_inv, rootChar_zsmul,
          D.rootChar_pairTuple_one, D.rootChar_pairTuple_zero, ← zpow_natCast]
        exact ((zpow_pair_iff ζ q D.ε).2 hζ).symm
      · show rootChar (D.pairTuple q ζ η) (w • f4Col D.B (f4Index 2)) =
          rootChar (D.pairTuple q ζ η) (f4Col D.B (f4Index 2)) ^ q
        rw [D.smul_two, D.rootChar_pairTuple_three, D.rootChar_pairTuple_two, zpow_natCast]
      · show rootChar (D.pairTuple q ζ η) (w • f4Col D.B (f4Index 3)) =
          rootChar (D.pairTuple q ζ η) (f4Col D.B (f4Index 3)) ^ q
        rw [D.smul_three, sub_eq_add_neg, rootChar_add, rootChar_neg_eq_inv, rootChar_zsmul,
          D.rootChar_pairTuple_three, D.rootChar_pairTuple_two, ← zpow_natCast]
        exact ((zpow_pair_iff η q D.ε).2 hη).symm
    rw [hsmul, hc, rootChar_pow_tuple]

@[expose] def torus (L : Type) [Field L] (q d : ℕ) : Subgroup (ModGL .F4 L) :=
  ((rootsOfUnity d L).prod (rootsOfUnity d L)).map
    ((rootDiagUnitHom .F4 L).comp (D.pairTupleHom q))

theorem rootDiagUnit_mem_torus_iff
    (q d : ℕ) (c : Fin Tag.F4.rank → Lˣ) :
    rootDiagUnit .F4 c ∈ D.torus L q d ↔
      ∃ ζ η : Lˣ, ζ ^ d = 1 ∧ η ^ d = 1 ∧ c = D.pairTuple q ζ η := by
  constructor
  · rintro ⟨⟨ζ, η⟩, ⟨hζ, hη⟩, h⟩
    exact ⟨ζ, η, (mem_rootsOfUnity d ζ).1 hζ, (mem_rootsOfUnity d η).1 hη,
      (rootDiagUnit_injective h).symm⟩
  · rintro ⟨ζ, η, hζ, hη, rfl⟩
    exact ⟨(ζ, η), ⟨(mem_rootsOfUnity d ζ).2 hζ, (mem_rootsOfUnity d η).2 hη⟩, rfl⟩

theorem torus_le_torusGroup (q d : ℕ) : D.torus L q d ≤ torusGroup .F4 L := by
  rintro _ ⟨x, -, rfl⟩
  exact F4_rootDiagUnit_mem_torusGroup _

variable (L) in
@[expose] def torusEquiv (q d : ℕ) : (rootsOfUnity d L × rootsOfUnity d L) ≃* D.torus L q d :=
  (Subgroup.prodEquiv _ _).symm.trans (Subgroup.equivMapOfInjective _ _
    (rootDiagUnit_injective.comp (D.pairTupleHom_injective q)))

theorem natCard_torus [IsAlgClosed L] (q d : ℕ) [NeZero (d : L)] :
    Nat.card (D.torus L q d) = d ^ 2 := by
  have : NeZero d := ⟨fun h => NeZero.ne (d : L) (by rw [h, Nat.cast_zero])⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := L) (n := d)
  rw [← Nat.card_congr (D.torusEquiv L q d).toEquiv, Nat.card_prod, hζ.card_rootsOfUnity, sq]

theorem nonempty_torus_mulEquiv [IsAlgClosed L] (q d : ℕ) [NeZero (d : L)] :
    Nonempty (D.torus L q d ≃* Multiplicative (ZMod d) × Multiplicative (ZMod d)) := by
  have : NeZero d := ⟨fun h => NeZero.ne (d : L) (by rw [h, Nat.cast_zero])⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := L) (n := d)
  have e : rootsOfUnity d L ≃* Multiplicative (ZMod d) :=
    mulEquivOfCyclicCardEq (by rw [hζ.card_rootsOfUnity]; simp)
  exact ⟨(D.torusEquiv L q d).symm.trans (MulEquiv.prodCongr e e)⟩

theorem conj_frob_eq_iff_mem_torus
    (F : L →+* L) {q : ℕ} (hF : ∀ c, F c = c ^ q) {d : ℕ}
    (hd : (d : ℤ) = (q : ℤ) ^ 2 - D.ε * q + 1) {u : ModGL .F4 L}
    (hu : u ∈ torusGroup .F4 L) :
    canonicalRep (coxeterSystem .F4) L w * Units.map (entrywiseHom F) u *
        (canonicalRep (coxeterSystem .F4) L w)⁻¹ = u ↔ u ∈ D.torus L q d := by
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hu
  rw [conj_frob_rootDiagUnit_eq_iff F hF w c, D.forall_rootChar_smul_eq_pow_iff,
    D.rootDiagUnit_mem_torus_iff, ← hd]
  simp only [zpow_natCast]

theorem mem_torus_iff_of_dvd {q p d : ℕ} (hpd : p ∣ d) {h : ModGL .F4 L} :
    h ∈ D.torus L q p ↔ h ∈ D.torus L q d ∧ h ^ p = 1 := by
  constructor
  · rintro ⟨⟨ζ, η⟩, ⟨hζ, hη⟩, rfl⟩
    refine ⟨⟨(ζ, η), ⟨rootsOfUnity_le_of_dvd hpd hζ, rootsOfUnity_le_of_dvd hpd hη⟩, rfl⟩, ?_⟩
    have h1 : ((ζ, η) : Lˣ × Lˣ) ^ p = 1 :=
      Prod.ext ((mem_rootsOfUnity p ζ).1 hζ) ((mem_rootsOfUnity p η).1 hη)
    rw [← map_pow, h1, map_one]
  · rintro ⟨⟨⟨ζ, η⟩, -, rfl⟩, hp⟩
    have h1 : ((ζ, η) : Lˣ × Lˣ) ^ p = 1 := by
      refine rootDiagUnit_injective.comp (D.pairTupleHom_injective q) ?_
      change (rootDiagUnitHom .F4 L).comp (D.pairTupleHom q) ((ζ, η) ^ p) =
        (rootDiagUnitHom .F4 L).comp (D.pairTupleHom q) 1
      rw [map_pow, hp, map_one]
    exact ⟨(ζ, η), ⟨(mem_rootsOfUnity p ζ).2 (congrArg Prod.fst h1),
      (mem_rootsOfUnity p η).2 (congrArg Prod.snd h1)⟩, rfl⟩

theorem exists_ne_one_mem_torus_torusRootChar_eq_one [IsAlgClosed L] (q : ℕ) {p : ℕ}
    (hp : p.Prime) [NeZero (p : L)] {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α) :
    ∃ h ∈ D.torus L q p, h ≠ 1 ∧ torusRootChar h α = 1 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.prim (M := L) (n := p)
  have hcard := hξ.card_rootsOfUnity
  let χ : (Fin Tag.F4.rank → Lˣ) →* Lˣ :=
    { toFun := fun c => rootChar c α
      map_one' := by simp [rootChar]
      map_mul' := fun a b => by
        simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib] }
  let ψ : (rootsOfUnity p L × rootsOfUnity p L) →* Lˣ := χ.comp ((D.pairTupleHom q).comp
    (MonoidHom.prodMap (rootsOfUnity p L).subtype (rootsOfUnity p L).subtype))
  have hψ : ∀ x, ψ x ∈ rootsOfUnity p L := fun x => by
    rw [mem_rootsOfUnity, ← map_pow]
    have : x ^ p = 1 := Prod.ext (Subtype.ext ((mem_rootsOfUnity p _).1 x.1.2))
      (Subtype.ext ((mem_rootsOfUnity p _).1 x.2.2))
    rw [this, map_one]
  let ψ' := ψ.codRestrict (rootsOfUnity p L) hψ
  obtain ⟨x, hx1, hxψ⟩ : ∃ x, x ≠ 1 ∧ ψ x = 1 := by
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective ψ' := (injective_iff_map_eq_one ψ').2 fun x hx =>
      by_contra fun h => hcon x h (congrArg Subtype.val hx)
    have hle := Nat.card_le_card_of_injective ψ' hinj
    rw [Nat.card_prod, hcard] at hle
    nlinarith [hp.two_le]
  refine ⟨rootDiagUnit .F4 (D.pairTuple q (x.1 : Lˣ) (x.2 : Lˣ)),
    ⟨((x.1 : Lˣ), (x.2 : Lˣ)), ⟨x.1.2, x.2.2⟩, rfl⟩, fun h1 => hx1 ?_, ?_⟩
  · have h2 : D.pairTupleHom q ((x.1 : Lˣ), (x.2 : Lˣ)) = D.pairTupleHom q 1 := by
      rw [map_one]
      exact rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)
    have h3 := D.pairTupleHom_injective q h2
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h3)) (Subtype.ext (congrArg Prod.snd h3))
  · rw [torusRootChar_rootDiagUnit _ hα]
    exact congrArg Units.val hxψ

end F4PairBasis

theorem exists_inv_mul_entrywise_eq (K : Type) [Field K] [Finite K] {Ω : Type} [Field Ω]
    [IsAlgClosed Ω] [Algebra K Ω] (F : Ω →+* Ω) (hF : ∀ c, F c = c ^ Nat.card K) (τ : Tag)
    {x : ModGL τ Ω} (hx : x ∈ adjointGroup τ Ω) :
    ∃ g ∈ adjointGroup τ Ω, g⁻¹ * Units.map (entrywiseHom F) g = x := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hℓ : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  obtain ⟨e, -, hqe⟩ := FiniteField.card K (ringChar K)
  have : CharP Ω (ringChar K) := charP_of_injective_algebraMap (algebraMap K Ω).injective _
  have : ExpChar Ω (ringChar K) := ExpChar.prime hℓ
  have hFe : iterateFrobenius Ω (ringChar K) e = F := RingHom.ext fun c => by
    rw [iterateFrobenius_def, hF, Nat.card_eq_fintype_card, hqe]
  obtain ⟨S, hS, hLang⟩ :=
    (exceptional_all_characteristic_field_Lang_surjectivity (ringChar K) Ω (e : ℕ) e.pos).1 τ
  obtain ⟨g, hg⟩ := hLang ⟨x, hx⟩
  refine ⟨g, g.2, ?_⟩
  have h := congrArg Subtype.val hg
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
  rw [hS, hFe] at h
  exact h.symm

theorem conjEntrywiseImage_inv_eq_fixed
    {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4) {K M : Type}
    [Field K] [Finite K] [Field M] [Algebra K M] (Fr : M →+* M)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (hbij : Function.Bijective Fr) {g n : ModGL τ M}
    (hg : g ∈ adjointGroup τ M) (hgn : g⁻¹ * Units.map (entrywiseHom Fr) g = n) :
    conjEntrywiseImage K g⁻¹ =
      adjointGroup τ M ⊓ (twistedEntrywise n Fr).eqLocus (MonoidHom.id _) := by
  have hfix := frobenius_fixed_eq_map_of_bijective (k := K) hτ Fr hFr hbij
  have hFg : Units.map (entrywiseHom Fr) g = g * n := by rw [← hgn, mul_inv_cancel_left]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxF : baseChangeGL (algebraMap K M) x ∈ adjointGroup τ M ⊓
        (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
      rw [hfix]
      exact ⟨x, hx, rfl⟩
    obtain ⟨hxC, hxσ⟩ := Subgroup.mem_inf.1 hxF
    have hxσ' : Units.map (entrywiseHom Fr) (baseChangeGL (algebraMap K M) x) =
        baseChangeGL (algebraMap K M) x := hxσ
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hg) hxC) hg, ?_⟩
    change twistedEntrywise n Fr (g⁻¹ * baseChangeGL (algebraMap K M) x * g) =
      g⁻¹ * baseChangeGL (algebraMap K M) x * g
    rw [twistedEntrywise_apply, map_mul, map_mul, map_inv, hxσ', hFg]
    group
  · intro hy
    obtain ⟨hyC, hyF⟩ := Subgroup.mem_inf.1 hy
    have hyF' : n * Units.map (entrywiseHom Fr) y * n⁻¹ = y := hyF
    have hu : g * y * g⁻¹ ∈ adjointGroup τ M ⊓
        (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
      refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hg hyC) (inv_mem hg), ?_⟩
      change Units.map (entrywiseHom Fr) (g * y * g⁻¹) = g * y * g⁻¹
      rw [map_mul, map_mul, map_inv, hFg]
      calc g * n * Units.map (entrywiseHom Fr) y * (g * n)⁻¹ =
            g * (n * Units.map (entrywiseHom Fr) y * n⁻¹) * g⁻¹ := by group
        _ = g * y * g⁻¹ := by rw [hyF']
    rw [hfix] at hu
    obtain ⟨x, hx, hxu⟩ := hu
    refine ⟨x, hx, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hxu]
    group

theorem map_conj_le_of_le_conjEntrywiseImage_inv
    {τ : Tag} {K M : Type} [Field K] [Field M]
    [Algebra K M] {g : ModGL τ M} {T₀ : Subgroup (ModGL τ M)}
    (h : T₀ ≤ conjEntrywiseImage K g⁻¹) :
    T₀.map (MulAut.conj g).toMonoidHom ≤
      (adjointGroup τ K).map (baseChangeGL (algebraMap K M)) := by
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨x, hx, hxu⟩ := h hu
  refine ⟨x, hx, ?_⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    inv_inv] at hxu ⊢
  rw [← hxu]
  group

theorem units_map_entrywiseHom_pow {τ : Tag} {M : Type} [Field M] (F : M →+* M) (m : ℕ)
    (y : ModGL τ M) :
    Units.map (entrywiseHom (F ^ m)) y = (Units.map (entrywiseHom F))^[m] y := by
  induction m generalizing y with
  | zero =>
    ext1
    exact entrywise_id _
  | succ m ih =>
    rw [Function.iterate_succ_apply, ← ih, pow_succ]
    ext1
    exact (entrywise_entrywise _ _ _).symm

theorem iterate_entrywise_eq_of_conj {τ : Tag} {M : Type} [Field M] (F : M →+* M)
    {n y : ModGL τ M} (hn : Units.map (entrywiseHom F) n = n)
    (hy : n * Units.map (entrywiseHom F) y * n⁻¹ = y) (j : ℕ) :
    (Units.map (entrywiseHom F))^[j] y = (n ^ j)⁻¹ * y * n ^ j := by
  have hFy : Units.map (entrywiseHom F) y = n⁻¹ * y * n :=
    calc Units.map (entrywiseHom F) y = n⁻¹ * (n * Units.map (entrywiseHom F) y * n⁻¹) * n := by
          group
      _ = n⁻¹ * y * n := by rw [hy]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, map_mul, map_mul, map_inv, map_pow, hn, hFy,
      pow_succ']
    group

theorem iterate_entrywise_eq_of_inv_mul {τ : Tag} {M : Type} [Field M] (F : M →+* M)
    {n g : ModGL τ M} (hn : Units.map (entrywiseHom F) n = n)
    (hg : g⁻¹ * Units.map (entrywiseHom F) g = n) (j : ℕ) :
    (Units.map (entrywiseHom F))^[j] g = g * n ^ j := by
  have hFg : Units.map (entrywiseHom F) g = g * n := by rw [← hg, mul_inv_cancel_left]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, map_mul, map_pow, hn, hFg, pow_succ', mul_assoc]

theorem mem_map_adjointGroup_of_iterate_eq
    {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4) {k M : Type}
    [Field k] [Finite k] [Field M] [Algebra k M] (F : M →+* M) {m : ℕ}
    (hFm : ∀ c, (F ^ m) c = c ^ Nat.card k) (hbij : Function.Bijective F) {y : ModGL τ M}
    (hy : y ∈ adjointGroup τ M) (hfix : (Units.map (entrywiseHom F))^[m] y = y) :
    y ∈ (adjointGroup τ k).map (baseChangeGL (algebraMap k M)) := by
  have hbij' : Function.Bijective (F ^ m) := by
    rw [RingHom.coe_pow]
    exact hbij.iterate m
  rw [← frobenius_fixed_eq_map_of_bijective hτ (F ^ m) hFm hbij']
  refine Subgroup.mem_inf.2 ⟨hy, ?_⟩
  change Units.map (entrywiseHom (F ^ m)) y = y
  rw [units_map_entrywiseHom_pow, hfix]

theorem rootDiagUnit_mem_map_torusGroup
    {k M : Type} [Field k] [Finite k] [Field M]
    [Algebra k M] {c : Fin Tag.F4.rank → Mˣ} (hc : ∀ j, (c j : M) ^ Nat.card k = c j) :
    rootDiagUnit .F4 c ∈ (torusGroup .F4 k).map (baseChangeGL (algebraMap k M)) := by
  choose s hs using fun j => mem_range_algebraMap_of_pow_card_eq (hc j)
  have hs0 : ∀ j, s j ≠ 0 := fun j h0 => (c j).ne_zero (by rw [← hs j, h0, map_zero])
  refine ⟨rootDiagUnit .F4 fun j => Units.mk0 (s j) (hs0 j),
    F4_rootDiagUnit_mem_torusGroup _, ?_⟩
  rw [baseChangeGL_rootDiagUnit]
  congr 1
  funext j
  exact Units.ext (hs j)

theorem F4_exists_charRootKernel_eq
    {L : Type} [Field L] (F : L →+* L) {q : ℕ}
    (hF : ∀ c, F c = c ^ q) {p : ℕ} [Fact p.Prime] {ξ : Lˣ} (hξ : orderOf ξ = p)
    (w : WeylGroup .F4) {x : ModGL .F4 L} (hxH : x ∈ torusGroup .F4 L)
    (hfix : canonicalRep (coxeterSystem .F4) L w * Units.map (entrywiseHom F) x *
      (canonicalRep (coxeterSystem .F4) L w)⁻¹ = x) (hxp : x ^ p = 1) (hx1 : x ≠ 1) :
    ∃ v : Fin Tag.F4.rank → ZMod p, v ≠ 0 ∧
      (dualMatrix (ZMod p) w).mulVec v = (q : ZMod p) • v ∧
      {α | IsRoot .F4 α ∧ torusRootChar x α = 1} = charRootKernel v := by
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hxH
  have hcp : c ^ p = 1 :=
    rootDiagUnit_injective (by rw [← rootDiagUnit_pow, hxp, rootDiagUnit_one])
  have hci : ∀ i, c i ^ p = 1 := fun i => by simpa using congrFun hcp i
  choose v hv using fun i => exists_pow_val_eq_of_pow_eq_one hξ (hci i)
  have hcv : c = fun i => ξ ^ (v i).val := funext fun i => (hv i).symm
  have hw := (conj_frob_rootDiagUnit_eq_iff F hF w c).1 hfix
  have hχ : ∀ l, rootChar c l = ξ ^ (charVal v l).val := fun l => by
    rw [hcv, rootChar_pow_val_eq hξ]
  have hval : ∀ l, charVal v (w • l) = charVal v l * (q : ZMod p) := fun l => by
    have h := hw l
    rw [hχ, hχ, ← pow_mul, pow_eq_pow_iff_modEq, hξ, ← ZMod.natCast_eq_natCast_iff] at h
    push_cast [ZMod.natCast_zmod_val] at h
    exact h
  have hdual : (dualMatrix (ZMod p) w).mulVec v = (q : ZMod p) • v := by
    funext j
    have h := hval (Pi.single j 1)
    rw [← charVal_dualMatrix, charVal_single, charVal_single] at h
    rw [h, Pi.smul_apply, smul_eq_mul, mul_comm]
  refine ⟨v, fun hv0 => hx1 ?_, hdual, ?_⟩
  · rw [hcv, hv0]
    convert (rootDiagUnit_one : rootDiagUnit .F4 (1 : Fin Tag.F4.rank → Lˣ) = 1) using 2
    funext i
    simp
  · ext α
    simp only [Set.mem_ofPred_eq, charRootKernel]
    constructor
    · rintro ⟨hα, h1⟩
      refine ⟨hα, eq_of_pow_val_eq_pow_val hξ ?_⟩
      rw [torusRootChar_rootDiagUnit c hα, hχ] at h1
      rw [Units.val_eq_one.1 h1, ZMod.val_zero, pow_zero]
    · rintro ⟨hα, h0⟩
      refine ⟨hα, ?_⟩
      rw [torusRootChar_rootDiagUnit c hα, hχ, h0, ZMod.val_zero, pow_zero, Units.val_one]

theorem F4_inf_centralizer_eq_of_root_kernel_empty
    {L : Type} [Field L] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) {Γ : Subgroup (ModGL .F4 L)} (hΓ : Γ ≤ adjointGroup .F4 L)
    {x : ModGL .F4 L} (hxH : x ∈ torusGroup .F4 L) (hxp : orderOf x = p)
    (hreg : {α | IsRoot .F4 α ∧ torusRootChar x α = 1} = ∅) :
    Γ ⊓ Subgroup.centralizer {x} = torusGroup .F4 L ⊓ Γ := by
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hxH
  have hX := F4_centralizer_eq_torusGroup_of_regular hp hp3 hxp fun α hα h1 => by
    have h : α ∈ {α | IsRoot .F4 α ∧ torusRootChar (rootDiagUnit .F4 c) α = 1} :=
      ⟨hα, by rw [torusRootChar_rootDiagUnit c hα, h1, Units.val_one]⟩
    rw [hreg] at h
    exact h
  rw [inf_comm (torusGroup .F4 L), ← hX, ← inf_assoc, inf_of_le_left hΓ]

theorem exists_sylow_map_le_and_conj_of_not_dvd_index {G H : Type*} [Group G] [Finite G]
    [Group H] {p : ℕ} [Fact p.Prime] (φ : G →* H) {T : Subgroup H}
    (hidx : ¬ p ∣ (T.comap φ).index) :
    (∃ S : Sylow p G, (S : Subgroup G).map φ ≤ T) ∧
      ∀ P : Subgroup G, IsPGroup p P →
        ∃ c : G, (P.map (MulAut.conj c).toMonoidHom).map φ ≤ T := by
  refine ⟨?_, fun P hP => ?_⟩
  · obtain ⟨S, hS⟩ := exists_sylow_le_of_not_dvd_index hidx
    exact ⟨S, Subgroup.map_le_iff_le_comap.2 hS⟩
  · obtain ⟨c, hc⟩ := exists_conj_map_le_of_not_dvd_index hidx hP
    exact ⟨c, Subgroup.map_le_iff_le_comap.2 hc⟩

theorem natCard_comap_of_le_range {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (hφ : Function.Injective φ) {T : Subgroup H} (hT : T ≤ φ.range) :
    Nat.card (T.comap φ) = Nat.card T := by
  rw [← Subgroup.card_map_of_injective hφ, Subgroup.map_comap_eq_self hT]

end CFSG.RankThree.Chevalley
