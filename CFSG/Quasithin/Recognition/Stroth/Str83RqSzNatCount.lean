module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4Frame
import CFSG.CGT.PushingUpLit.SolKNA.SzSimpleTransport
import CFSG.RankThree.GF2n.Tim81.Sec2.SzFixedPointwise
import CFSG.RankThree.GF2n.Tim81.Sec4.CentralTISzInputs
import CFSG.Goldschmidt75.Sig3Trans

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Blueprint
open CFSG.RankThree.GF2n.Tim81.Sec2 CFSG.RankThree.GF2n.Tim81.CentralTI
open CFSG.CGT.PushingUpLit.SolKNA CFSG.CGT.Timmesfeld75 CFSG.LieType.Ree
open CFSG.QuasithinUnique.Setup.X7
open scoped Matrix

variable {G : Type} [Group G]

private def szc_Intertwines {H N : Subgroup G} {a : ℕ}
    (e : oTwoQuot ↥H ≃* ↥(Sz a)) (c : ℕ)
    (φ : ↥N →* Multiplicative (Fin 4 → GaloisField 2 (2 * a + 1))) : Prop :=
  ∀ (h : ↥H) (x y : ↥N), (y : G) = (h : G) * (x : G) * (h : G)⁻¹ →
    Multiplicative.toAdd (φ y) =
      ((((e (QuotientGroup.mk h) : ↥(Sz a)) : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))).map (· ^ 2 ^ c)) *ᵥ
      Multiplicative.toAdd (φ x)

private noncomputable def szc_mat (a c : ℕ) (g : suzukiGroup a (GaloisField 2 (2 * a + 1))) :
    Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1)) :=
  (((g : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
    Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))).map (· ^ 2 ^ c))

private noncomputable def szc_szRep (a c : ℕ) :
    Representation (ZMod 2) ↥(suzukiGroup a (GaloisField 2 (2 * a + 1)))
      (Fin 4 → GaloisField 2 (2 * a + 1)) where
  toFun g :=
    { toFun := fun v => szc_mat a c g *ᵥ v
      map_add' := fun v w => Matrix.mulVec_add (szc_mat a c g) v w
      map_smul' := fun r v => Matrix.mulVec_smul (szc_mat a c g) r v }
  map_one' := by
    apply LinearMap.ext
    intro v
    have h1 : szc_mat a c (1 : suzukiGroup a (GaloisField 2 (2 * a + 1))) = 1 := by
      ext i j
      by_cases hij : i = j
      · simp [szc_mat, Matrix.one_apply, hij]
      · simp [szc_mat, Matrix.one_apply, hij, zero_pow (pow_ne_zero c two_ne_zero)]
    change szc_mat a c (1 : suzukiGroup a (GaloisField 2 (2 * a + 1))) *ᵥ v = v
    rw [h1, Matrix.one_mulVec]
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    have hm : szc_mat a c (g * h) = szc_mat a c g * szc_mat a c h := by
      simp only [szc_mat, Subgroup.coe_mul, map_mul]
      exact matrix_map_pow_mul c _ _
    change szc_mat a c (g * h) *ᵥ v =
      szc_mat a c g *ᵥ (szc_mat a c h *ᵥ v)
    rw [hm, ← Matrix.mulVec_mulVec]

private theorem szc_isSzNatural (a c : ℕ) : IsSzNatural (szc_szRep a c) :=
  ⟨c, AddEquiv.refl _, fun _ _ => rfl⟩

private theorem szc_J_map_pow (a c : ℕ) :
    (CFSG.LinearAlgebra.exteriorSquareJ (GaloisField 2 (2 * a + 1))).map (· ^ 2 ^ c) =
      CFSG.LinearAlgebra.exteriorSquareJ (GaloisField 2 (2 * a + 1)) := by
  ext i j
  rw [Matrix.map_apply, CFSG.LinearAlgebra.exteriorSquareJ_apply]
  split_ifs with h
  · simp [h]
  · simp [h, zero_pow (pow_ne_zero c two_ne_zero)]

private theorem szc_map_szEquiv (a c : ℕ) (g : suzukiGroup a (GaloisField 2 (2 * a + 1))) :
    ((((szEquiv a g : ↥(Sz a)) : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
      Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))).map (· ^ 2 ^ c)) =
      CFSG.LinearAlgebra.exteriorSquareJ (GaloisField 2 (2 * a + 1)) *
        szc_mat a c g * CFSG.LinearAlgebra.exteriorSquareJ (GaloisField 2 (2 * a + 1)) := by
  let K := GaloisField 2 (2 * a + 1)
  let J : Matrix (Fin 4) (Fin 4) K := CFSG.LinearAlgebra.exteriorSquareJ K
  have hJJ : J * J = 1 := exteriorSquareJ_mul_self K
  have h := szEquiv_mul_J a g
  have hA : (((szEquiv a g : ↥(Sz a)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      J * (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) * J := by
    calc (((szEquiv a g : ↥(Sz a)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
        = (((szEquiv a g : ↥(Sz a)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * J * J := by
          rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = J * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * J := by rw [h]
  change ((((szEquiv a g : ↥(Sz a)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map
      (· ^ 2 ^ c)) = J * szc_mat a c g * J
  rw [hA]
  simp only [szc_mat]
  rw [matrix_map_pow_mul, matrix_map_pow_mul, szc_J_map_pow a c]

private theorem szc_J_mulVec_injective (a : ℕ) :
    Function.Injective fun v : Fin 4 → GaloisField 2 (2 * a + 1) =>
      CFSG.LinearAlgebra.exteriorSquareJ (GaloisField 2 (2 * a + 1)) *ᵥ v := by
  intro x y h
  let J : Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1)) :=
    CFSG.LinearAlgebra.exteriorSquareJ (GaloisField 2 (2 * a + 1))
  have hJJ : J * J = 1 := exteriorSquareJ_mul_self _
  change J *ᵥ x = J *ᵥ y at h
  calc x = (J * J) *ᵥ x := by rw [hJJ, Matrix.one_mulVec]
    _ = J *ᵥ (J *ᵥ x) := by rw [← Matrix.mulVec_mulVec]
    _ = J *ᵥ (J *ᵥ y) := by rw [h]
    _ = (J * J) *ᵥ y := by rw [Matrix.mulVec_mulVec]
    _ = y := by rw [hJJ, Matrix.one_mulVec]

private theorem szc_J_iff (a c : ℕ) (g : suzukiGroup a (GaloisField 2 (2 * a + 1)))
    (v : Fin 4 → GaloisField 2 (2 * a + 1)) :
    szc_szRep a c g (CFSG.LinearAlgebra.exteriorSquareJ (GaloisField 2 (2 * a + 1)) *ᵥ v) =
        CFSG.LinearAlgebra.exteriorSquareJ (GaloisField 2 (2 * a + 1)) *ᵥ v ↔
      ((((szEquiv a g : ↥(Sz a)) : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))).map (· ^ 2 ^ c)) *ᵥ v = v := by
  let K := GaloisField 2 (2 * a + 1)
  let J : Matrix (Fin 4) (Fin 4) K := CFSG.LinearAlgebra.exteriorSquareJ K
  let B : Matrix (Fin 4) (Fin 4) K := szc_mat a c g
  have hM : ((((szEquiv a g : ↥(Sz a)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map
      (· ^ 2 ^ c)) = J * B * J := szc_map_szEquiv a c g
  have hJ2 : ∀ w : Fin 4 → K, J *ᵥ (J *ᵥ w) = w := by
    intro w
    have hJJ : J * J = 1 := exteriorSquareJ_mul_self K
    rw [Matrix.mulVec_mulVec, hJJ, Matrix.one_mulVec]
  have hleft : szc_szRep a c g (J *ᵥ v) = B *ᵥ (J *ᵥ v) := rfl
  rw [hleft]
  constructor
  · intro h
    rw [hM]
    calc (J * B * J) *ᵥ v = J *ᵥ (B *ᵥ (J *ᵥ v)) := by
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ = J *ᵥ (J *ᵥ v) := by rw [h]
      _ = v := hJ2 v
  · intro h
    apply szc_J_mulVec_injective a
    calc J *ᵥ (B *ᵥ (J *ᵥ v)) = (J * B * J) *ᵥ v := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = ((((szEquiv a g : ↥(Sz a)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map
            (· ^ 2 ^ c)) *ᵥ v := by rw [← hM]
      _ = v := h
      _ = J *ᵥ (J *ᵥ v) := (hJ2 v).symm

private theorem szc_fixed_iff_conj
    {H N : Subgroup G} {a : ℕ} {c : ℕ} {e : oTwoQuot ↥H ≃* ↥(Sz a)}
    {φ : ↥N →* Multiplicative (Fin 4 → GaloisField 2 (2 * a + 1))}
    (hφinj : Function.Injective φ) (hφeq : szc_Intertwines e c φ)
    (hHN : H ≤ Subgroup.normalizer (N : Set G))
    {h : G} (hh : h ∈ H) (n : ↥N)
    (g : suzukiGroup a (GaloisField 2 (2 * a + 1)))
    (hg : e (QuotientGroup.mk ⟨h, hh⟩) = szEquiv a g) :
    szc_szRep a c g (CFSG.LinearAlgebra.exteriorSquareJ (GaloisField 2 (2 * a + 1)) *ᵥ
        Multiplicative.toAdd (φ n)) =
      CFSG.LinearAlgebra.exteriorSquareJ (GaloisField 2 (2 * a + 1)) *ᵥ
        Multiplicative.toAdd (φ n) ↔
      h * (n : G) * h⁻¹ = (n : G) := by
  let v : Fin 4 → GaloisField 2 (2 * a + 1) := Multiplicative.toAdd (φ n)
  have hM : ((((e (QuotientGroup.mk ⟨h, hh⟩) : ↥(Sz a)) : GL
        (Fin 4) (GaloisField 2 (2 * a + 1))) :
      Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))).map (· ^ 2 ^ c)) =
      ((((szEquiv a g : ↥(Sz a)) : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))).map (· ^ 2 ^ c)) := by
    rw [hg]
  rw [szc_J_iff a c g (Multiplicative.toAdd (φ n))]
  let y : ↥N :=
    ⟨h * (n : G) * h⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hHN hh) (n : G)).mp n.2⟩
  have hy : Multiplicative.toAdd (φ y) =
      ((((szEquiv a g : ↥(Sz a)) : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))).map (· ^ 2 ^ c)) *ᵥ
        Multiplicative.toAdd (φ n) := by
    have h := hφeq ⟨h, hh⟩ n y rfl
    rw [hM] at h
    simpa [y] using h
  constructor
  · intro hv
    have hyv : Multiplicative.toAdd (φ y) = Multiplicative.toAdd (φ n) := by
      rw [hy, hv]
    have hyn : y = n := hφinj (by
      simpa using congrArg Multiplicative.ofAdd hyv)
    exact congrArg Subtype.val hyn
  · intro hconj
    have hyn : y = n := Subtype.ext hconj
    have hv : Multiplicative.toAdd (φ n) =
        ((((szEquiv a g : ↥(Sz a)) : GL (Fin 4) (GaloisField 2 (2 * a + 1))) :
          Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * a + 1))).map (· ^ 2 ^ c)) *ᵥ
          Multiplicative.toAdd (φ n) := by
      rw [← hy, hyn]
    exact hv.symm

private theorem szc_J_mulVec_mem_fixedSub_iff
    {H N : Subgroup G} {a : ℕ} {c : ℕ} {e : oTwoQuot ↥H ≃* ↥(Sz a)}
    {φ : ↥N →* Multiplicative (Fin 4 → GaloisField 2 (2 * a + 1))}
    (hφinj : Function.Injective φ) (hφeq : szc_Intertwines e c φ)
    (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (X : Subgroup ↥H) (n : ↥N) :
    CFSG.LinearAlgebra.exteriorSquareJ (GaloisField 2 (2 * a + 1)) *ᵥ
        Multiplicative.toAdd (φ n) ∈
      fixedSub (szc_szRep a c)
        ((X.map (QuotientGroup.mk' (pCore 2 ↥H))).map
          (e.trans (szEquiv a).symm).toMonoidHom) ↔
      (n : G) ∈ Subgroup.centralizer (X.map (Subgroup.subtype H) : Set G) := by
  rw [mem_fixedSub]
  constructor
  · intro hfix
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hg : e (QuotientGroup.mk x) =
        szEquiv a ((e.trans (szEquiv a).symm) (QuotientGroup.mk x)) := by
      simp
    have hconj := (szc_fixed_iff_conj hφinj hφeq hHN x.2 n
      ((e.trans (szEquiv a).symm) (QuotientGroup.mk x)) hg).mp
      (hfix _ (Subgroup.mem_map_of_mem _
        (Subgroup.mem_map_of_mem (QuotientGroup.mk' (pCore 2 ↥H)) hx)))
    calc ((x : ↥H) : G) * (n : G)
        = (((x : ↥H) : G) * (n : G) * ((x : ↥H) : G)⁻¹) * ((x : ↥H) : G) := by group
      _ = (n : G) * ((x : ↥H) : G) := by rw [hconj]
  · intro hcent y hy
    obtain ⟨yq, hyq, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hyq
    have hg : e (QuotientGroup.mk x) =
        szEquiv a ((e.trans (szEquiv a).symm) (QuotientGroup.mk x)) := by
      simp
    apply (szc_fixed_iff_conj hφinj hφeq hHN x.2 n
      ((e.trans (szEquiv a).symm) (QuotientGroup.mk x)) hg).mpr
    have hcomm := (Subgroup.mem_centralizer_iff.mp hcent) ((x : ↥H) : G)
      (Subgroup.mem_map_of_mem (Subgroup.subtype H) hx)
    calc ((x : ↥H) : G) * (n : G) * ((x : ↥H) : G)⁻¹
        = ((n : G) * ((x : ↥H) : G)) * ((x : ↥H) : G)⁻¹ := by rw [hcomm]
      _ = (n : G) := by group

private theorem szc_card_inf_centralizer_eq_fixedSub
    {H N : Subgroup G} {a : ℕ} {c : ℕ} {e : oTwoQuot ↥H ≃* ↥(Sz a)}
    {φ : ↥N →* Multiplicative (Fin 4 → GaloisField 2 (2 * a + 1))}
    (hφsurj : Function.Surjective φ) (hφker : φ.ker = (⊥ : Subgroup G).subgroupOf N)
    (hφeq : szc_Intertwines e c φ)
    (hHN : H ≤ Subgroup.normalizer (N : Set G))
    (X : Subgroup ↥H) :
    Nat.card ↥(N ⊓ Subgroup.centralizer (X.map (Subgroup.subtype H) : Set G)) =
      Nat.card (fixedSub (szc_szRep a c)
        ((X.map (QuotientGroup.mk' (pCore 2 ↥H))).map
          (e.trans (szEquiv a).symm).toMonoidHom)) := by
  classical
  let K := GaloisField 2 (2 * a + 1)
  let J : Matrix (Fin 4) (Fin 4) K := CFSG.LinearAlgebra.exteriorSquareJ K
  have hφinj : Function.Injective φ :=
    (MonoidHom.ker_eq_bot_iff φ).mp (by simpa using hφker)
  let φe : ↥N ≃ (Fin 4 → K) :=
    (Equiv.ofBijective φ ⟨hφinj, hφsurj⟩).trans Multiplicative.toAdd
  have hφe : ∀ n : ↥N, φe n = Multiplicative.toAdd (φ n) := fun _ => rfl
  let C : Subgroup G := Subgroup.centralizer (X.map (Subgroup.subtype H) : Set G)
  let F : Submodule (ZMod 2) (Fin 4 → K) :=
    fixedSub (szc_szRep a c)
      ((X.map (QuotientGroup.mk' (pCore 2 ↥H))).map
        (e.trans (szEquiv a).symm).toMonoidHom)
  have hmem : ∀ n : ↥N, J *ᵥ φe n ∈ F ↔ (n : G) ∈ C := by
    intro n
    rw [hφe n]
    exact szc_J_mulVec_mem_fixedSub_iff hφinj hφeq hHN X n
  have hJ2 : ∀ w : Fin 4 → K, J *ᵥ (J *ᵥ w) = w := by
    intro w
    have hJJ : J * J = 1 := exteriorSquareJ_mul_self K
    rw [Matrix.mulVec_mulVec, hJJ, Matrix.one_mulVec]
  refine Nat.card_congr ?_
  refine
    { toFun := fun n : ↥(N ⊓ C) =>
        ⟨J *ᵥ φe ⟨n.1, (Subgroup.mem_inf.mp n.2).1⟩,
          (hmem ⟨n.1, (Subgroup.mem_inf.mp n.2).1⟩).2 (Subgroup.mem_inf.mp n.2).2⟩
      invFun := fun v : ↥F =>
        ⟨((φe.symm (J *ᵥ (v : Fin 4 → K)) : ↥N) : G),
          Subgroup.mem_inf.mpr
            ⟨(φe.symm (J *ᵥ (v : Fin 4 → K)) : ↥N).2,
              (hmem (φe.symm (J *ᵥ (v : Fin 4 → K)))).1 (by
                rw [Equiv.apply_symm_apply, hJ2]
                exact v.2)⟩⟩
      left_inv := fun n => by
        apply Subtype.ext
        change ((φe.symm (J *ᵥ (J *ᵥ φe (⟨n.1, (Subgroup.mem_inf.mp n.2).1⟩))) : ↥N) : G) =
          n.1
        rw [hJ2, Equiv.symm_apply_apply]
      right_inv := fun v => by
        apply Subtype.ext
        change J *ᵥ φe (φe.symm (J *ᵥ (v : Fin 4 → K))) = (v : Fin 4 → K)
        rw [Equiv.apply_symm_apply, hJ2] }

private theorem szc_fixedSub_zpowers_eq_of_mem_conj_szZ
    {a : ℕ} (hK : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1))
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) ↥(suzukiGroup a (GaloisField 2 (2 * a + 1))) W)
    (hρ : IsSzNatural ρ)
    {z g : suzukiGroup a (GaloisField 2 (2 * a + 1))}
    (hz : z ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g
      (szZ a (GaloisField 2 (2 * a + 1)))) (hz1 : z ≠ 1) :
    fixedSub ρ (Subgroup.zpowers z) =
      fixedSub ρ (CFSG.CGT.Timmesfeld75.conjSubgroup g (szZ a (GaloisField 2 (2 * a + 1)))) := by
  let K := GaloisField 2 (2 * a + 1)
  letI : Fintype K := Fintype.ofFinite K
  let w : suzukiGroup a K := suzukiWElt a K
  have hsz : szZ a K = CFSG.CGT.Timmesfeld75.conjSubgroup w (suzukiZ0 a K) := rfl
  have hconj : CFSG.CGT.Timmesfeld75.conjSubgroup g (szZ a K) =
      (suzukiZ0 a K).map (MulAut.conj (g * w)).toMonoidHom := by
    rw [hsz, CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
    rfl
  have hz' : z ∈ (suzukiZ0 a K).map (MulAut.conj (g * w)).toMonoidHom := by
    rwa [← hconj]
  obtain ⟨z1, hz1Z, hz1eq⟩ := Subgroup.mem_map.mp hz'
  have hz1ne : z1 ≠ 1 := by
    intro h
    apply hz1
    rw [← hz1eq, h, map_one]
  have hzp : (Subgroup.zpowers z1).map (MulAut.conj (g * w)).toMonoidHom =
      Subgroup.zpowers z := by
    rw [MonoidHom.map_zpowers, hz1eq]
  calc fixedSub ρ (Subgroup.zpowers z)
      = fixedSub ρ ((Subgroup.zpowers z1).map (MulAut.conj (g * w)).toMonoidHom) := by
          rw [hzp]
    _ = (fixedSub ρ (Subgroup.zpowers z1)).map (ρ (g * w)) :=
          fixedSub_map_conj ρ (g * w) (Subgroup.zpowers z1)
    _ = (fixedSub ρ (suzukiZ0 a K)).map (ρ (g * w)) := by
          rw [fixedSub_zpowers_eq_fixedSub_suzukiZ0 hK ρ hρ hz1Z hz1ne]
    _ = fixedSub ρ ((suzukiZ0 a K).map (MulAut.conj (g * w)).toMonoidHom) :=
          (fixedSub_map_conj ρ (g * w) (suzukiZ0 a K)).symm
    _ = fixedSub ρ (CFSG.CGT.Timmesfeld75.conjSubgroup g (szZ a K)) := by rw [hconj]

private theorem szc_natCard_fixedSub_zpowers_of_mem_conj_szZ
    {a : ℕ} (hK : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1))
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) ↥(suzukiGroup a (GaloisField 2 (2 * a + 1))) W)
    (hρ : IsSzNatural ρ)
    {z g : suzukiGroup a (GaloisField 2 (2 * a + 1))}
    (hz : z ∈ CFSG.CGT.Timmesfeld75.conjSubgroup g
      (szZ a (GaloisField 2 (2 * a + 1)))) (hz1 : z ≠ 1) :
    Nat.card (fixedSub ρ (Subgroup.zpowers z)) =
      Nat.card (GaloisField 2 (2 * a + 1)) ^ 2 := by
  letI : Fintype (GaloisField 2 (2 * a + 1)) := Fintype.ofFinite _
  rw [szc_fixedSub_zpowers_eq_of_mem_conj_szZ hK ρ hρ hz hz1]
  exact natCard_fixedSub_conj_szZ hK ρ hρ g

theorem natCard_inf_centralizer_sylow_of_isSzNaturalSection
    {H N T : Subgroup G} {a : ℕ} (hN : IsSzNaturalSection H N ⊥ a)
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hT : IsSylowTwoOf T H) :
    Nat.card ↥(N ⊓ Subgroup.centralizer (T : Set G)) = 2 ^ (2 * a + 1) := by
  classical
  obtain ⟨e, c, φ, hφsurj, hφker, hφeq⟩ := hN
  let K := GaloisField 2 (2 * a + 1)
  letI : Fintype K := Fintype.ofFinite K
  let e0 : oTwoQuot ↥H ≃* suzukiGroup a K := e.trans (szEquiv a).symm
  let ρ : Representation (ZMod 2) ↥(suzukiGroup a K) (Fin 4 → K) := szc_szRep a c
  have hφeq' : szc_Intertwines e c φ := hφeq
  have hK : Nat.card K = 2 ^ (2 * a + 1) := GaloisField.card 2 (2 * a + 1) (by omega)
  have hρ : IsSzNatural ρ := szc_isSzNatural a c
  have hcard := szc_card_inf_centralizer_eq_fixedSub (X := T.subgroupOf H)
    hφsurj hφker hφeq' hHN
  have hTmap : (T.subgroupOf H).map (Subgroup.subtype H) = T :=
    Subgroup.map_subgroupOf_eq_of_le hT.1
  rw [hTmap] at hcard
  rw [hcard]
  let X' : Subgroup ↥(suzukiGroup a K) :=
    ((T.subgroupOf H).map (QuotientGroup.mk' (pCore 2 ↥H))).map e0.toMonoidHom
  change Nat.card (fixedSub ρ X') = 2 ^ (2 * a + 1)
  have hX' : IsSylowTwoOf X' ⊤ := by
    have hSylH : IsSylowTwoOf (T.subgroupOf H) ⊤ :=
      CFSG.Quasithin.H13.NQCat.A314D.isSylowTwoOf_top_subgroupOf hT
    have hSylQ : IsSylowTwoOf ((T.subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 ↥H))) ⊤ :=
      CFSG.Quasithin.isSylowTwoOf_top_map_of_surjective hSylH _
        (QuotientGroup.mk'_surjective _)
    exact CFSG.Quasithin.isSylowTwoOf_top_map_of_surjective hSylQ e0.toMonoidHom e0.surjective
  have hU : IsSylowTwoOf (suzukiU a K) ⊤ :=
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.suzukiU_isSylowTwoOf hK
  obtain ⟨g, -, hg⟩ := CFSG.Quasithin.B6.isSylowTwoOf_exists_conj hU hX'
  calc Nat.card (fixedSub ρ X')
      = Nat.card (fixedSub ρ (suzukiU a K)) := by
        rw [hg]
        exact natCard_fixedSub_map_conj ρ g (suzukiU a K)
    _ = Nat.card K := natCard_fixedSub_suzukiU hK ρ hρ
    _ = 2 ^ (2 * a + 1) := hK

theorem natCard_inf_centralizer_of_isSzNaturalSection
    {H N : Subgroup G} {a : ℕ} {x : G} (hN : IsSzNaturalSection H N ⊥ a)
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hxH : x ∈ H)
    (hx2 : x * x ∈ pCoreOf 2 H) (hxQ : x ∉ pCoreOf 2 H) :
    Nat.card ↥(N ⊓ Subgroup.centralizer ({x} : Set G)) = (2 ^ (2 * a + 1)) ^ 2 := by
  classical
  obtain ⟨e, c, φ, hφsurj, hφker, hφeq⟩ := hN
  let K := GaloisField 2 (2 * a + 1)
  letI : Fintype K := Fintype.ofFinite K
  let e0 : oTwoQuot ↥H ≃* suzukiGroup a K := e.trans (szEquiv a).symm
  let ρ : Representation (ZMod 2) ↥(suzukiGroup a K) (Fin 4 → K) := szc_szRep a c
  have hφeq' : szc_Intertwines e c φ := hφeq
  have hK : Nat.card K = 2 ^ (2 * a + 1) := GaloisField.card 2 (2 * a + 1) (by omega)
  have hρ : IsSzNatural ρ := szc_isSzNatural a c
  let xH : ↥H := ⟨x, hxH⟩
  let y : oTwoQuot ↥H := QuotientGroup.mk' (pCore 2 ↥H) xH
  let z : suzukiGroup a K := e0 y
  have hx2' : xH * xH ∈ pCore 2 ↥H :=
    (F1.mem_pCore_iff_coe (xH * xH)).mpr (by simpa [xH] using hx2)
  have hy2 : y * y = 1 := by
    have h : y * y = QuotientGroup.mk' (pCore 2 ↥H) (xH * xH) := (map_mul _ xH xH).symm
    rw [h]
    exact (QuotientGroup.eq_one_iff (xH * xH)).mpr hx2'
  have hy1 : y ≠ 1 := by
    intro hy
    apply hxQ
    have hxmem : xH ∈ pCore 2 ↥H := by
      simpa only [y, QuotientGroup.mk'_apply] using (QuotientGroup.eq_one_iff xH).mp hy
    exact (F1.mem_pCore_iff_coe xH).mp hxmem
  have hz2 : z * z = 1 := by
    rw [show z * z = e0 (y * y) from (map_mul e0 y y).symm, hy2, map_one]
  have hz1 : z ≠ 1 := by
    intro hz
    apply hy1
    exact e0.injective (by simpa [z] using hz)
  have hK' : Fintype.card K = 2 ^ (2 * a + 1) := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  obtain ⟨g, hgz⟩ :=
    CFSG.RankThree.GF2n.Tim81.CentralTI.exists_conjSubgroup_szZ_of_involution hK' hz2 hz1
  let X : Subgroup ↥H := Subgroup.zpowers xH
  have hXmap : X.map (Subgroup.subtype H) = Subgroup.zpowers x := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hXmap' : (X.map (QuotientGroup.mk' (pCore 2 ↥H))).map e0.toMonoidHom =
      Subgroup.zpowers z := by
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  have hcard := szc_card_inf_centralizer_eq_fixedSub (X := X)
    hφsurj hφker hφeq' hHN
  rw [hXmap, hXmap'] at hcard
  rw [← CFSG.Goldschmidt75.centralizer_zpowers_eq x, hcard]
  rw [szc_natCard_fixedSub_zpowers_of_mem_conj_szZ hK ρ hρ hgz hz1, hK]

end CFSG.Quasithin.Stroth
