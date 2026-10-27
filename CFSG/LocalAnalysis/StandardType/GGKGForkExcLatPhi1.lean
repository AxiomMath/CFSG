module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLat3
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcLat4

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE

@[expose]
def ggKGEp_iota : Fin Tag.E6.rank → Fin 4 := ![0, 1, 2, 3, 2, 0]

@[expose]
def ggKGEp_sec : Fin 4 → Fin Tag.E6.rank := ![0, 1, 2, 3]

@[expose] def ggKGEp_phi : Equiv.Perm (Fin Tag.E6.rank) :=
  Equiv.swap ⟨0, by decide⟩ ⟨5, by decide⟩ * Equiv.swap ⟨2, by decide⟩ ⟨4, by decide⟩

theorem ggKGEp_iota_phi (i : Fin Tag.E6.rank) :
    ggKGEp_iota (ggKGEp_phi i) = ggKGEp_iota i := by
  fin_cases i <;> decide +kernel

theorem ggKGEp_iota_sec (i : Fin 4) : ggKGEp_iota (ggKGEp_sec i) = i := by
  fin_cases i <;> decide +kernel

@[expose]
def ggKGEp_io (y : Fin 4 → ℤ) : Fin Tag.E6.rank → ℤ := fun i => y (ggKGEp_iota i)

theorem ggKGEp_eq_or_eq_phi_sec (i : Fin Tag.E6.rank) :
    i = ggKGEp_sec (ggKGEp_iota i) ∨ i = ggKGEp_phi (ggKGEp_sec (ggKGEp_iota i)) := by
  fin_cases i <;> decide +kernel

@[expose]
noncomputable def ggKGEp_w0 (τ : Tag) : WeylGroup τ :=
  (coxeterSystem τ).wordProd ((RootOps.longestWord τ).map τ.idx)

theorem ggKGEp_w0_smul_E6
    (i : Fin Tag.E6.rank) :
    ggKGEp_w0 .E6 • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) = -Pi.single (ggKGEp_phi i) 1 := by
  fin_cases i <;> (rw [ggKGEp_w0, wordProd_smul] <;> decide +kernel)

theorem ggKGEp_w0_reversesSigns_E6 :
    ReversesSigns (ggKGEp_w0 .E6) := by
  intro α hα hpos
  refine height_smul_neg_of_forall_single (fun i => ?_) hα hpos
  rw [ggKGEp_w0_smul_E6 i]
  simp [height]

theorem ggKGEp_w0_inv_E6 :
    (ggKGEp_w0 .E6)⁻¹ = ggKGEp_w0 .E6 :=
  (ReversesSigns.eq (ggKGEp_w0_reversesSigns_E6)
    (ReversesSigns.inv (ggKGEp_w0_reversesSigns_E6))).symm

theorem ggKGEp_eq_w0_of_longest
    {w : WeylGroup Tag.E6} (hw : ExcIsLongest Tag.E6 w) : w = ggKGEp_w0 .E6 := by
  refine ReversesSigns.eq ?_ ggKGEp_w0_reversesSigns_E6
  intro α hα hpos
  exact (IsRoot.height_neg_iff (IsRoot.smul hα w)).2
    (hw α hα ((IsRoot.height_pos_iff hα).1 hpos))

theorem ggKGEp_weylTuple_w0_phi
    {K : Type} [Field K] (c : Fin Tag.E6.rank → Kˣ) :
    weylTuple (ggKGEp_w0 .E6) c = fun i => (c (ggKGEp_phi i))⁻¹ := by
  funext i
  rw [weylTuple, ggKGEp_w0_inv_E6, ggKGEp_w0_smul_E6 i,
    show (-Pi.single (ggKGEp_phi i) 1 : Fin Tag.E6.rank → ℤ) = 0 - Pi.single (ggKGEp_phi i) 1 by
      simp,
    rootChar_sub, rootChar_zero, one_mul]
  rw [show rootChar c (Pi.single (ggKGEp_phi i) 1) = c (ggKGEp_phi i) from by
    simpa using rootChar_nsmul_single c (ggKGEp_phi i) 1]

private theorem ggKGEp_units_map_fr_eq_pow
    {K : Type} [Field K] (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (u : (AlgebraicClosure K)ˣ) :
    Units.map Fr.toMonoidHom u = u ^ Nat.card K := by
  apply Units.ext
  rw [Units.coe_map]
  change Fr ↑u = ↑u ^ Nat.card K
  rw [hFr]

private theorem ggKGEp_units_map_fr_inv_eq_self
    {K : Type} [Field K] {p : ℕ} (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {b : (AlgebraicClosure K)ˣ} (hb : b ^ p = 1)
    {k : ℕ} (hq : Nat.card K = p * k - 1) (hpk : 1 ≤ p * k) :
    (Units.map Fr.toMonoidHom b)⁻¹ = b := by
  rw [ggKGEp_units_map_fr_eq_pow Fr hFr b, hq]
  have h1 : b ^ (p * k) = 1 := by rw [pow_mul, hb, one_pow]
  have h2 : b ^ (p * k - 1) = b⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel hpk, h1]
  rw [h2, inv_inv]

theorem ggKGEp_phi_fixed_of_mem_torus
    {K : Type} [Field K] [Finite K] {p : ℕ} {E : Subgroup (adjointGroup Tag.E6 K)}
    (F : ExcFrame Tag.E6 K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    (hlong : ExcIsLongest Tag.E6 F.w) (hpq : p ∣ Nat.card K + 1)
    {b : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ} (hb : ∀ i, b i ^ p = 1)
    (hT : rootDiagUnit Tag.E6 b ∈ F.D.torus) :
    ∀ i, b (ggKGEp_phi i) = b i := by
  have hΦd : F.D.Φ (rootDiagUnit Tag.E6 b) =
      rootDiagUnit Tag.E6 (fun i => Units.map Fr.toMonoidHom (b i)) := by
    rw [hΦ]
    exact Units.ext (entrywise_rootDiag Fr b)
  have hmem : F.D.n * F.D.Φ (rootDiagUnit Tag.E6 b) * F.D.n⁻¹ = rootDiagUnit Tag.E6 b :=
    (mem_twistedTorusOf.1 hT).2
  rw [hΦd, F.n_eq, canonicalRep_conj_rootDiagUnit] at hmem
  have hwt : weylTuple F.w (fun i => Units.map Fr.toMonoidHom (b i)) = b :=
    rootDiagUnit_injective hmem
  rw [ggKGEp_eq_w0_of_longest hlong, ggKGEp_weylTuple_w0_phi] at hwt
  obtain ⟨k, hk⟩ := hpq
  have hpos : 0 < Nat.card K := by
    haveI : Nonempty K := ⟨0⟩
    exact Nat.card_pos
  have hq : Nat.card K = p * k - 1 := by omega
  have hpk : 1 ≤ p * k := by omega
  intro i
  have hi := congrFun hwt i
  rw [ggKGEp_units_map_fr_inv_eq_self Fr hFr (hb (ggKGEp_phi i)) hq hpk] at hi
  exact hi

noncomputable def ggKGEp_pick
    {K : Type} [Field K] [Finite K] {p : ℕ} {E : Subgroup (adjointGroup Tag.E6 K)}
    (hp : p.Prime) (hp5 : 5 ≤ p) (F : ExcFrame Tag.E6 K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (hlong : ExcIsLongest Tag.E6 F.w) (hpq : p ∣ Nat.card K + 1)
    (y : Fin 4 → ℤ) : ↥E :=
  let b : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ := fun i => ζ ^ y (ggKGEp_iota i)
  let hb : ∀ i, b i ^ p = 1 := fun i => ggKGEl_zetaPow_pow_eq_one ζ hζ (y (ggKGEp_iota i))
  let hfix : ∀ i, b (ggKGEx_phi i) = b i :=
    ggKGEx_phi_fix (by dsimp only [b]; rfl) (by dsimp only [b]; rfl)
  let h := ggKGEx_exists_conj_of_hact hp (by omega) (fun _ => hp5) (Or.inl rfl) F hΦ (b := b) hb
    (ggKGEx_hact_w_phi F hFr hlong hpq hb hfix)
  ⟨Classical.choose h, (Classical.choose_spec h).1⟩

theorem ggKGEp_pick_spec
    {K : Type} [Field K] [Finite K] {p : ℕ} {E : Subgroup (adjointGroup Tag.E6 K)}
    (hp : p.Prime) (hp5 : 5 ≤ p) (F : ExcFrame Tag.E6 K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (hlong : ExcIsLongest Tag.E6 F.w) (hpq : p ∣ Nat.card K + 1)
    (y : Fin 4 → ℤ) :
    F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (((ggKGEp_pick hp hp5 F hFr hΦ ζ hζ hlong hpq y : ↥E) : adjointGroup Tag.E6 K) :
          ModGL Tag.E6 K) * F.D.g0 =
      rootDiagUnit Tag.E6 (fun i => ζ ^ y (ggKGEp_iota i)) := by
  dsimp only [ggKGEp_pick]
  let b : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ := fun i => ζ ^ y (ggKGEp_iota i)
  have hb : ∀ i, b i ^ p = 1 := fun i => ggKGEl_zetaPow_pow_eq_one ζ hζ (y (ggKGEp_iota i))
  have hfix : ∀ i, b (ggKGEx_phi i) = b i :=
    ggKGEx_phi_fix (by dsimp only [b]; rfl) (by dsimp only [b]; rfl)
  exact (Classical.choose_spec (ggKGEx_exists_conj_of_hact hp (by omega) (fun _ => hp5) (Or.inl rfl) F hΦ
    (b := b) hb
    (ggKGEx_hact_w_phi F hFr hlong hpq (b := b) hb hfix))).2.symm

noncomputable def ggKGEp_pi
    {K : Type} [Field K] [Finite K] {p : ℕ} {E : Subgroup (adjointGroup Tag.E6 K)}
    (hp : p.Prime) (hp5 : 5 ≤ p) (F : ExcFrame Tag.E6 K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (hlong : ExcIsLongest Tag.E6 F.w) (hpq : p ∣ Nat.card K + 1) :
    (Fin 4 → ℤ) →+ Additive ↥E where
  toFun y := Additive.ofMul (ggKGEp_pick hp hp5 F hFr hΦ ζ hζ hlong hpq y)
  map_zero' := by
    change Additive.ofMul (ggKGEp_pick hp hp5 F hFr hΦ ζ hζ hlong hpq 0) =
      Additive.ofMul (1 : ↥E)
    apply congrArg Additive.ofMul
    apply Subtype.ext
    apply ggKGEl_conj_injective F
    dsimp only
    rw [ggKGEp_pick_spec, Subgroup.coe_one, ggKGEl_conj_one]
    simp only [Pi.zero_apply, zpow_zero, Pi.one_apply]
    exact rootDiagUnit_one
  map_add' y y' := by
    change Additive.ofMul (ggKGEp_pick hp hp5 F hFr hΦ ζ hζ hlong hpq (y + y')) =
      Additive.ofMul (ggKGEp_pick hp hp5 F hFr hΦ ζ hζ hlong hpq y *
        ggKGEp_pick hp hp5 F hFr hΦ ζ hζ hlong hpq y')
    apply congrArg Additive.ofMul
    apply Subtype.ext
    apply ggKGEl_conj_injective F
    dsimp only
    rw [ggKGEp_pick_spec, Subgroup.coe_mul, ggKGEl_conj_mul, ggKGEp_pick_spec, ggKGEp_pick_spec]
    rw [show (fun i => ζ ^ (y + y') (ggKGEp_iota i)) =
        (fun i => ζ ^ y (ggKGEp_iota i)) * (fun i => ζ ^ y' (ggKGEp_iota i)) from by
      funext i; simp [Pi.add_apply, zpow_add]]
    rw [rootDiagUnit_mul]

theorem ggKGEp_pi_spec
    {K : Type} [Field K] [Finite K] {p : ℕ} {E : Subgroup (adjointGroup Tag.E6 K)}
    (hp : p.Prime) (hp5 : 5 ≤ p) (F : ExcFrame Tag.E6 K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (hlong : ExcIsLongest Tag.E6 F.w) (hpq : p ∣ Nat.card K + 1)
    (y : Fin 4 → ℤ) :
    F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (((Additive.toMul (ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq y) : ↥E) :
          adjointGroup Tag.E6 K) : ModGL Tag.E6 K) * F.D.g0 =
      rootDiagUnit Tag.E6 (fun i => ζ ^ y (ggKGEp_iota i)) :=
  ggKGEp_pick_spec hp hp5 F hFr hΦ ζ hζ hlong hpq y

theorem ggKGEp_pi_surjective
    {K : Type} [Field K] [Finite K] {p : ℕ} {E : Subgroup (adjointGroup Tag.E6 K)}
    (hp : p.Prime) (hp5 : 5 ≤ p) (F : ExcFrame Tag.E6 K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (hlong : ExcIsLongest Tag.E6 F.w) (hpq : p ∣ Nat.card K + 1) :
    Function.Surjective (ggKGEp_pi hp hp5 F hFr hΦ ζ hζ hlong hpq) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro e
  let Ψ : ↥E →* ModGL Tag.E6 (AlgebraicClosure K) :=
    { toFun := fun x => F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) * F.D.g0
      map_one' := ggKGEl_conj_one F
      map_mul' := fun a b => ggKGEl_conj_mul F (a : adjointGroup Tag.E6 K) (b : adjointGroup Tag.E6 K) }
  have he : ((Additive.toMul e : ↥E) : adjointGroup Tag.E6 K) ^ p = 1 :=
    ((F.mem_iff ((Additive.toMul e : ↥E) : adjointGroup Tag.E6 K)).1 (Additive.toMul e).2).1
  have heT : F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (((Additive.toMul e : ↥E) : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) * F.D.g0 ∈ F.D.torus :=
    ((F.mem_iff ((Additive.toMul e : ↥E) : adjointGroup Tag.E6 K)).1 (Additive.toMul e).2).2
  have heG : F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (((Additive.toMul e : ↥E) : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) * F.D.g0 ∈
      torusGroup Tag.E6 (AlgebraicClosure K) := (mem_twistedTorusOf.1 heT).1
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup heG
  have hbp : ∀ i, b i ^ p = 1 := by
    have h1 : (rootDiagUnit Tag.E6 b) ^ p = 1 := by
      rw [← hb]
      change (Ψ (Additive.toMul e)) ^ p = 1
      rw [← map_pow, show (Additive.toMul e : ↥E) ^ p = 1 from Subtype.ext he, map_one]
    have hbp' : b ^ p = 1 := rootDiagUnit_injective (τ := Tag.E6)
      (by rw [← rootDiagUnit_pow, h1, rootDiagUnit_one])
    intro i
    simpa using congrFun hbp' i
  have hbfix : ∀ i, b (ggKGEp_phi i) = b i :=
    ggKGEp_phi_fixed_of_mem_torus F hFr hΦ hlong hpq hbp (hb ▸ heT)
  choose y hy using fun i => ggKGEl_eq_zetaPow_of_pow_eq_one ζ hζ (hbp (ggKGEp_sec i))
  refine ⟨y, ?_⟩
  apply Additive.toMul.injective
  apply Subtype.ext
  apply ggKGEl_conj_injective F
  dsimp only
  rw [ggKGEp_pi_spec, hb]
  congr 1
  funext i
  rcases ggKGEp_eq_or_eq_phi_sec i with h | h
  · rw [h, ggKGEp_iota_sec]
    exact (hy (ggKGEp_iota i)).symm
  · rw [h, hbfix, ggKGEp_iota_phi, ggKGEp_iota_sec]
    exact (hy (ggKGEp_iota i)).symm

end CFSG.StandardType

end
