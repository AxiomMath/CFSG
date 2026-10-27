module

public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGDefs
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGLift
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerMain
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Torus

public section

namespace CFSG.StandardType.UnitSixThreeKG

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD CFSG.Assembly CFSG.StandardType

variable {K : Type} [Field K] {n : ℕ}

private theorem mk_eq_one_of_mem_blockSU {T : Finset (Fin 6)} (hT : T ≠ Finset.univ)
    {x : ↥(unitarySU 2 n K 6)} (hx : x ∈ blockSU (n := n) (K := K) T)
    (hπ : LargeEvenProjMk (unitarySU 2 n K 6) x = 1) : x = 1 := by
  obtain ⟨c, hc⟩ := TableBUD.exists_scalar_of_mk_eq (x := x) (y := 1) (by rw [hπ, map_one])
  have hc' : (x : GL (Fin 6) K)⁻¹ = GeneralLinearGroup.scalar (Fin 6) c := by
    simpa using hc
  have hxscal : (x : GL (Fin 6) K) = GeneralLinearGroup.scalar (Fin 6) c⁻¹ := by
    have h := congrArg Inv.inv hc'
    simpa using h
  have hi : ∃ i : Fin 6, i ∉ T := by
    by_contra h
    push Not at h
    exact hT (Finset.eq_univ_of_forall h)
  obtain ⟨i, hi⟩ := hi
  have hblock := TableBUE.mem_blockSU.mp hx
  have h1 : ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i i = 1 := by
    simpa using hblock i i (Or.inl hi)
  have h2 : ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i i = ((c : K))⁻¹ := by
    rw [hxscal, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
    exact Units.val_inv_eq_inv_val c
  have hcu : (↑c : K) = 1 := inv_eq_one.mp (by rw [← h2, h1])
  have hc1 : c = 1 := Units.ext hcu
  have hx1 : (x : GL (Fin 6) K) = 1 := by
    rw [hxscal, hc1, inv_one, map_one]
  exact Subtype.ext hx1

private theorem diagHom_mem_blockSU_of_supp {S : Finset (Fin 6)} {t : Fin 6 → Kˣ}
    (ht : ∀ i ∉ S, t i = 1) (hmem : diagHom 6 t ∈ unitarySU 2 n K 6) :
    (⟨diagHom 6 t, hmem⟩ : ↥(unitarySU 2 n K 6)) ∈ blockSU (n := n) (K := K) S := by
  rw [TableBUE.mem_blockSU]
  rintro i j hij
  by_cases h : i = j
  · subst h
    have hi : i ∉ S := by rcases hij with h | h <;> assumption
    change ((diagHom 6 t : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i i =
      (1 : Matrix (Fin 6) (Fin 6) K) i i
    rw [coe_diagHom, Matrix.diagonal_apply_eq, ht i hi, Units.val_one, Matrix.one_apply_eq]
  · change ((diagHom 6 t : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j =
      (1 : Matrix (Fin 6) (Fin 6) K) i j
    rw [coe_diagHom, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

private noncomputable def suppVec (S : Finset (Fin 6)) (b : Fin S.card → Kˣ) :
    Fin 6 → Kˣ :=
  fun i => if hi : i ∈ S then b (S.equivFin ⟨i, hi⟩) else 1

private theorem suppVec_apply_mem (S : Finset (Fin 6)) (b : Fin S.card → Kˣ) {i : Fin 6}
    (hi : i ∈ S) : suppVec S b i = b (S.equivFin ⟨i, hi⟩) := by
  simp [suppVec, hi]

private theorem suppVec_apply_not_mem (S : Finset (Fin 6)) (b : Fin S.card → Kˣ) {i : Fin 6}
    (hi : i ∉ S) : suppVec S b i = 1 := by
  simp [suppVec, hi]

private theorem suppVec_pow (S : Finset (Fin 6)) (b : Fin S.card → Kˣ)
    (hb : ∀ k, b k ^ 3 = 1) (i : Fin 6) : suppVec S b i ^ 3 = 1 := by
  by_cases hi : i ∈ S
  · rw [suppVec_apply_mem S b hi, hb]
  · rw [suppVec_apply_not_mem S b hi, one_pow]

private theorem suppVec_norm (S : Finset (Fin 6)) (b : Fin S.card → Kˣ)
    (hb : ∀ k, b k ^ (2 ^ n + 1) = 1) (i : Fin 6) :
    suppVec S b i ^ (2 ^ n + 1) = 1 := by
  by_cases hi : i ∈ S
  · rw [suppVec_apply_mem S b hi, hb]
  · rw [suppVec_apply_not_mem S b hi, one_pow]

private theorem suppVec_prod (S : Finset (Fin 6)) (b : Fin S.card → Kˣ) :
    ∏ i : Fin 6, suppVec S b i = ∏ k, b k := by
  rw [(Finset.prod_subset (Finset.subset_univ S)
      (fun x _ hx => suppVec_apply_not_mem S b hx)).symm,
    (Finset.prod_coe_sort S (suppVec S b)).symm]
  exact Fintype.prod_equiv S.equivFin (fun i : S => suppVec S b ↑i) b
    (fun x => suppVec_apply_mem S b x.2)

private noncomputable def genA (ω : Kˣ) : Fin 3 → Kˣ :=
  fun k => if k = 0 then ω else if k = 1 then ω⁻¹ else 1

private noncomputable def genB (ω : Kˣ) : Fin 3 → Kˣ :=
  fun k => if k = 0 then 1 else if k = 1 then ω else ω⁻¹

private theorem genA_pow (ω : Kˣ) (hω3 : ω ^ 3 = 1) (k : Fin 3) : genA ω k ^ 3 = 1 := by
  fin_cases k <;> simp [genA, hω3]

private theorem genB_pow (ω : Kˣ) (hω3 : ω ^ 3 = 1) (k : Fin 3) : genB ω k ^ 3 = 1 := by
  fin_cases k <;> simp [genB, hω3]

private theorem genA_norm (ω : Kˣ) (hωq : ω ^ (2 ^ n + 1) = 1) (k : Fin 3) :
    genA ω k ^ (2 ^ n + 1) = 1 := by
  fin_cases k <;> simp [genA, hωq]

private theorem genB_norm (ω : Kˣ) (hωq : ω ^ (2 ^ n + 1) = 1) (k : Fin 3) :
    genB ω k ^ (2 ^ n + 1) = 1 := by
  fin_cases k <;> simp [genB, hωq]

private noncomputable def c3 (ω : Kˣ) (S : Finset (Fin 6)) (hS : S.card = 3) (j : Fin 2) :
    Fin 6 → Kˣ :=
  suppVec S (fun k : Fin S.card => (if j = 0 then genA ω else genB ω) (Fin.cast hS k))

private theorem c3_pow (ω : Kˣ) (S : Finset (Fin 6)) (hS : S.card = 3) (hω3 : ω ^ 3 = 1) :
    ∀ j i, c3 ω S hS j i ^ 3 = 1 := by
  intro j i
  refine suppVec_pow S (fun k : Fin S.card =>
    (if j = 0 then genA ω else genB ω) (Fin.cast hS k)) (fun k => ?_) i
  by_cases hj : j = 0
  · subst hj; simpa using genA_pow ω hω3 (Fin.cast hS k)
  · rw [if_neg hj]; exact genB_pow ω hω3 (Fin.cast hS k)

private theorem c3_prod (ω : Kˣ) (S : Finset (Fin 6)) (hS : S.card = 3) (hω3 : ω ^ 3 = 1) :
    ∀ j, ∏ i, c3 ω S hS j i = 1 := by
  intro j
  rw [show c3 ω S hS j = suppVec S (fun k : Fin S.card =>
    (if j = 0 then genA ω else genB ω) (Fin.cast hS k)) from rfl, suppVec_prod]
  by_cases hj : j = 0
  · subst hj
    rw [if_pos rfl, Fintype.prod_equiv (Fin.castOrderIso hS).toEquiv
        (fun k : Fin S.card => genA ω (Fin.cast hS k)) (genA ω) (fun k => rfl),
      Fin.prod_univ_three]
    simp [genA, hω3]
  · rw [if_neg hj, Fintype.prod_equiv (Fin.castOrderIso hS).toEquiv
        (fun k : Fin S.card => genB ω (Fin.cast hS k)) (genB ω) (fun k => rfl),
      Fin.prod_univ_three]
    simp [genB, hω3]

private theorem c3_norm (ω : Kˣ) (S : Finset (Fin 6)) (hS : S.card = 3)
    (hωq : ω ^ (2 ^ n + 1) = 1) : ∀ j i, c3 ω S hS j i ^ (2 ^ n + 1) = 1 := by
  intro j i
  refine suppVec_norm S (fun k : Fin S.card =>
    (if j = 0 then genA ω else genB ω) (Fin.cast hS k)) (fun k => ?_) i
  by_cases hj : j = 0
  · subst hj; simpa using genA_norm ω hωq (Fin.cast hS k)
  · rw [if_neg hj]; exact genB_norm ω hωq (Fin.cast hS k)

private theorem c3_priv (ω : Kˣ) (S : Finset (Fin 6)) (hS : S.card = 3)
    (hωo : orderOf ω = 3) :
    ∀ j : Fin 2, ∃ i : Fin 6, (∀ j', j' ≠ j → c3 ω S hS j' i = 1) ∧
      orderOf (c3 ω S hS j i) = 3 := by
  intro j
  have hmem : ∀ k : Fin 3, (↑(S.equivFin.symm (Fin.cast hS.symm k)) : Fin 6) ∈ S :=
    fun k => (S.equivFin.symm (Fin.cast hS.symm k)).2
  have hcast : ∀ k : Fin 3, Fin.cast hS (S.equivFin ⟨↑(S.equivFin.symm (Fin.cast hS.symm k)),
      hmem k⟩) = k := by
    intro k
    simp
  by_cases hj : j = 0
  · subst hj
    refine ⟨↑(S.equivFin.symm (Fin.cast hS.symm 0)), ?_, ?_⟩
    · intro j' hj'
      have hj'1 : j' = 1 := by fin_cases j' <;> simp_all
      subst hj'1
      rw [show c3 ω S hS 1 = suppVec S (fun k : Fin S.card => genB ω (Fin.cast hS k)) from by
        funext i; simp [c3]]
      rw [suppVec_apply_mem S _ (hmem 0), hcast 0]
      simp [genB]
    · rw [show c3 ω S hS 0 = suppVec S (fun k : Fin S.card => genA ω (Fin.cast hS k)) from by
        funext i; simp [c3]]
      rw [suppVec_apply_mem S _ (hmem 0), hcast 0]
      simpa [genA] using hωo
  · have hj1 : j = 1 := by fin_cases j <;> simp_all
    subst hj1
    refine ⟨↑(S.equivFin.symm (Fin.cast hS.symm 2)), ?_, ?_⟩
    · intro j' hj'
      have hj'0 : j' = 0 := by fin_cases j' <;> simp_all
      subst hj'0
      rw [show c3 ω S hS 0 = suppVec S (fun k : Fin S.card => genA ω (Fin.cast hS k)) from by
        funext i; simp [c3]]
      rw [suppVec_apply_mem S _ (hmem 2), hcast 2]
      simp [genA]
    · rw [show c3 ω S hS 1 = suppVec S (fun k : Fin S.card => genB ω (Fin.cast hS k)) from by
        funext i; simp [c3]]
      rw [suppVec_apply_mem S _ (hmem 2), hcast 2]
      have hinv : orderOf (ω⁻¹) = 3 := by rw [orderOf_inv, hωo]
      simpa [genB] using hinv


private theorem c3_supp (ω : Kˣ) (S : Finset (Fin 6)) (hS : S.card = 3) (hω3 : ω ^ 3 = 1)
    (a : Multiplicative (Fin 2 → ZMod 3)) {i : Fin 6} (hi : i ∉ S) :
    CFSG.RankThree.Classical2.expHom (c3 ω S hS) (c3_pow ω S hS hω3) a i = 1 := by
  rw [CFSG.RankThree.Classical2.expHom_apply]
  refine Finset.prod_eq_one fun j _ => ?_
  have h1 : c3 ω S hS j i = 1 := suppVec_apply_not_mem S _ hi
  rw [h1, one_pow]

private theorem exists_pgroup_le_blockSU (hKd : UnitaryFieldData 2 n K)
    {B : Subgroup ↥(unitarySU 2 n K 6)} {T : Finset (Fin 6)} (hT : T ≠ Finset.univ)
    (hBle : B ≤ blockSU (n := n) (K := K) T)
    {θ : Multiplicative (Fin 2 → ZMod 3) →* (Fin 6 → Kˣ)}
    (hθ : Function.Injective θ)
    (hmem : ∀ a, diagHom 6 (θ a) ∈ unitarySU 2 n K 6)
    (hblk : ∀ a, (⟨diagHom 6 (θ a), hmem a⟩ : ↥(unitarySU 2 n K 6)) ∈ B) :
    ∃ P : Subgroup (LargeEvenProj (unitarySU 2 n K 6)), IsPGroup 3 P ∧ ¬ IsCyclic P ∧
      P ≤ B.map (LargeEvenProjMk (unitarySU 2 n K 6)) ∧
      3 ∣ Nat.card (B.map (LargeEvenProjMk (unitarySU 2 n K 6))) := by
  classical
  let π := LargeEvenProjMk (unitarySU 2 n K 6)
  let Φ : Multiplicative (Fin 2 → ZMod 3) →* ↥(unitarySU 2 n K 6) :=
    ((diagHom 6).comp θ).codRestrict _ hmem
  let Ψ : Multiplicative (Fin 2 → ZMod 3) →* LargeEvenProj (unitarySU 2 n K 6) := π.comp Φ
  have hΦinj : Function.Injective Φ := by
    intro a b hab
    have h1 : (diagHom 6) (θ a) = (diagHom 6) (θ b) := congrArg Subtype.val hab
    exact hθ (diagHom_injective 6 h1)
  have hΦle : Φ.range ≤ B := by
    rintro _ ⟨a, rfl⟩
    exact hblk a
  have hΨinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h2 : π (Φ a) = 1 := ha
    have h3 : Φ a = 1 := mk_eq_one_of_mem_blockSU hT (hBle (hΦle ⟨a, rfl⟩)) h2
    exact hΦinj (by rw [h3, map_one])
  have hpow3 : ∀ a : Multiplicative (Fin 2 → ZMod 3), a ^ 3 = 1 := by
    intro a
    rw [← toAdd_eq_zero, toAdd_pow]
    funext i
    have h3 : (3 : ZMod 3) = 0 := ZMod.natCast_self 3
    fin_cases i <;> simp [Pi.smul_apply, nsmul_eq_mul, h3]
  have hdom : IsPGroup 3 (Multiplicative (Fin 2 → ZMod 3)) :=
    IsPGroup.of_exponent_dvd_pow (n := 1) (by
      rw [pow_one]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow3)
  have hPpg : IsPGroup 3 ↥Ψ.range :=
    IsPGroup.of_surjective hdom Ψ.rangeRestrict (MonoidHom.rangeRestrict_surjective Ψ)
  have hcard9 : Nat.card (Multiplicative (Fin 2 → ZMod 3)) = 9 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hcardP : Nat.card ↥Ψ.range = 9 := by
    rw [(Nat.card_congr (MonoidHom.ofInjective hΨinj).toEquiv).symm, hcard9]
  let s : Multiplicative (Fin 2 → ZMod 3) := Multiplicative.ofAdd (Pi.single 0 (1 : ZMod 3))
  have hs3 : s ^ 3 = 1 := hpow3 s
  have hsne : s ≠ 1 := by
    intro h
    have h1 := congrFun (congrArg Multiplicative.toAdd h) 0
    simp [s] at h1
  have hΨs3 : Ψ s ^ 3 = 1 := by rw [← map_pow, hs3, map_one]
  have hΨsne : Ψ s ≠ 1 := fun h => hsne (hΨinj (by rw [h, map_one]))
  have hordP : orderOf (⟨Ψ s, ⟨s, rfl⟩⟩ : ↥Ψ.range) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      simpa [Subgroup.coe_pow, Subgroup.coe_one] using hΨs3
    · intro h
      exact hΨsne (Subtype.ext_iff.mp h)
  have h3dvd : 3 ∣ Monoid.exponent ↥Ψ.range := by
    have h := Monoid.order_dvd_exponent (⟨Ψ s, ⟨s, rfl⟩⟩ : ↥Ψ.range)
    rwa [hordP] at h
  have hexp_dvd : Monoid.exponent ↥Ψ.range ∣ 3 := by
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun g => ?_
    obtain ⟨a, ha⟩ := g.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← ha, ← map_pow, hpow3 a, map_one]
  have hexp : Monoid.exponent ↥Ψ.range = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hexp_dvd with h1 | h3
    · rw [h1] at h3dvd
      norm_num at h3dvd
    · exact h3
  have hnc : ¬ IsCyclic ↥Ψ.range :=
    (not_isCyclic_iff_exponent_eq_prime Nat.prime_three (by rw [hcardP]; norm_num)).mpr hexp
  have hΨrange : Ψ.range = Φ.range.map π := MonoidHom.range_comp π Φ
  have hle : Ψ.range ≤ B.map π := by
    rw [hΨrange]
    exact Subgroup.map_mono hΦle
  have h3div : 3 ∣ Nat.card ↥(B.map π) :=
    dvd_trans (by rw [hcardP]; norm_num) (Subgroup.card_dvd_of_le hle)
  exact ⟨Ψ.range, hPpg, hnc, hle, h3div⟩

private theorem exists_pgroup_le_blockSU_three (hKd : UnitaryFieldData 2 n K)
    (hpq : 3 ∣ 2 ^ n + 1) {S : Finset (Fin 6)} (hS : S.card = 3)
    (hT : S ≠ Finset.univ) :
    ∃ P : Subgroup (LargeEvenProj (unitarySU 2 n K 6)), IsPGroup 3 P ∧ ¬ IsCyclic P ∧
      P ≤ (blockSU (n := n) (K := K) S).map (LargeEvenProjMk (unitarySU 2 n K 6)) ∧
      3 ∣ Nat.card ((blockSU (n := n) (K := K) S).map (LargeEvenProjMk (unitarySU 2 n K 6))) := by
  obtain ⟨ω, hωo, hωq⟩ :=
    CFSG.RankThree.Classical2.exists_orderOf_eq_norm_one hKd Nat.prime_three hpq
  have hω3 : ω ^ 3 = 1 := hωo ▸ pow_orderOf_eq_one ω
  have hθinj : Function.Injective
      (CFSG.RankThree.Classical2.expHom (c3 ω S hS) (c3_pow ω S hS hω3)) :=
    CFSG.RankThree.Classical2.expHom_injective (c3 ω S hS) (c3_pow ω S hS hω3) (c3_priv ω S hS hωo)
  have hmem : ∀ a, diagHom 6 (CFSG.RankThree.Classical2.expHom (c3 ω S hS) (c3_pow ω S hS hω3) a) ∈
      unitarySU 2 n K 6 := fun a =>
    CFSG.RankThree.Classical2.diagHom_expHom_mem_unitarySU hKd (c3 ω S hS) (c3_pow ω S hS hω3)
      (c3_prod ω S hS hω3) (c3_norm ω S hS hωq) a
  have hblk : ∀ a, (⟨diagHom 6 (CFSG.RankThree.Classical2.expHom (c3 ω S hS)
      (c3_pow ω S hS hω3) a), hmem a⟩ :
      ↥(unitarySU 2 n K 6)) ∈ blockSU (n := n) (K := K) S := fun a =>
    diagHom_mem_blockSU_of_supp (fun i hi => c3_supp ω S hS hω3 a hi) (hmem a)
  exact exists_pgroup_le_blockSU hKd hT le_rfl hθinj hmem hblk

private theorem blockSU_mono {S T : Finset (Fin 6)} (h : S ⊆ T) :
    blockSU (n := n) (K := K) S ≤ blockSU (n := n) (K := K) T := by
  intro x hx
  rw [TableBUE.mem_blockSU] at hx ⊢
  intro i j hij
  exact hx i j (by
    rcases hij with hi | hj
    · exact Or.inl fun h' => hi (h h')
    · exact Or.inr fun h' => hj (h h'))

private noncomputable def gen2 (ω : Kˣ) : Fin 2 → Kˣ :=
  fun k => if k = 0 then ω else ω⁻¹

private theorem gen2_pow (ω : Kˣ) (hω3 : ω ^ 3 = 1) (k : Fin 2) : gen2 ω k ^ 3 = 1 := by
  fin_cases k <;> simp [gen2, hω3]

private theorem gen2_norm (ω : Kˣ) (hωq : ω ^ (2 ^ n + 1) = 1) (k : Fin 2) :
    gen2 ω k ^ (2 ^ n + 1) = 1 := by
  fin_cases k <;> simp [gen2, hωq]

private theorem gen2_prod (ω : Kˣ) (hω3 : ω ^ 3 = 1) : ∏ k : Fin 2, gen2 ω k = 1 := by
  rw [Fin.prod_univ_two]
  simp [gen2, hω3]

private noncomputable def c2 (ω : Kˣ) (S : Finset (Fin 6)) (hS : S.card = 2) : Fin 6 → Kˣ :=
  suppVec S (fun k : Fin S.card => gen2 ω (Fin.cast hS k))

private theorem c2_pow (ω : Kˣ) (S : Finset (Fin 6)) (hS : S.card = 2) (hω3 : ω ^ 3 = 1) :
    ∀ i, c2 ω S hS i ^ 3 = 1 :=
  suppVec_pow S _ (fun k => gen2_pow ω hω3 (Fin.cast hS k))

private theorem c2_prod (ω : Kˣ) (S : Finset (Fin 6)) (hS : S.card = 2) (hω3 : ω ^ 3 = 1) :
    ∏ i, c2 ω S hS i = 1 := by
  rw [show c2 ω S hS = suppVec S (fun k : Fin S.card => gen2 ω (Fin.cast hS k)) from rfl,
    suppVec_prod, Fintype.prod_equiv (Fin.castOrderIso hS).toEquiv
      (fun k : Fin S.card => gen2 ω (Fin.cast hS k)) (gen2 ω) (fun k => rfl)]
  exact gen2_prod ω hω3

private theorem c2_norm (ω : Kˣ) (S : Finset (Fin 6)) (hS : S.card = 2)
    (hωq : ω ^ (2 ^ n + 1) = 1) : ∀ i, c2 ω S hS i ^ (2 ^ n + 1) = 1 :=
  suppVec_norm S _ (fun k => gen2_norm ω hωq (Fin.cast hS k))

private theorem c2_supp (ω : Kˣ) (S : Finset (Fin 6)) (hS : S.card = 2) {i : Fin 6}
    (hi : i ∉ S) : c2 ω S hS i = 1 :=
  suppVec_apply_not_mem S _ hi

private theorem c2_mem_unitary (hKd : UnitaryFieldData 2 n K) (ω : Kˣ) (S : Finset (Fin 6))
    (hS : S.card = 2) (hω3 : ω ^ 3 = 1) (hωq : ω ^ (2 ^ n + 1) = 1) :
    diagHom 6 (c2 ω S hS) ∈ unitarySU 2 n K 6 := by
  refine Line63.H5.diagHom_mem_unitarySU hKd (fun i => ?_) ?_
  · rw [← Units.val_pow_eq_pow_val, c2_norm ω S hS hωq i, Units.val_one]
  · rw [← Units.coe_prod, c2_prod ω S hS hω3, Units.val_one]

private theorem c2_apply (ω : Kˣ) (S : Finset (Fin 6)) (hS : S.card = 2) {i : Fin 6}
    (hi : i ∈ S) : c2 ω S hS i = gen2 ω (Fin.cast hS (S.equivFin ⟨i, hi⟩)) := by
  rw [show c2 ω S hS = suppVec S (fun k : Fin S.card => gen2 ω (Fin.cast hS k)) from rfl,
    suppVec_apply_mem S _ hi]

private theorem c2_eq_gen2_zero (ω : Kˣ) (S : Finset (Fin 6)) (hS : S.card = 2) :
    c2 ω S hS (↑(S.equivFin.symm (Fin.cast hS.symm 0))) = ω := by
  have hmem : (↑(S.equivFin.symm (Fin.cast hS.symm 0)) : Fin 6) ∈ S :=
    (S.equivFin.symm (Fin.cast hS.symm 0)).2
  rw [c2_apply ω S hS hmem]
  have hcast : Fin.cast hS (S.equivFin ⟨↑(S.equivFin.symm (Fin.cast hS.symm 0)), hmem⟩) = 0 := by
    simp
  rw [hcast]
  simp [gen2]

private noncomputable def c22 (ω : Kˣ) (S₁ S₂ : Finset (Fin 6)) (hc₁ : S₁.card = 2)
    (hc₂ : S₂.card = 2) (j : Fin 2) : Fin 6 → Kˣ :=
  if j = 0 then c2 ω S₁ hc₁ else c2 ω S₂ hc₂

private theorem c22_zero (ω : Kˣ) (S₁ S₂ : Finset (Fin 6)) (hc₁ : S₁.card = 2)
    (hc₂ : S₂.card = 2) : c22 ω S₁ S₂ hc₁ hc₂ 0 = c2 ω S₁ hc₁ := by
  simp [c22]

private theorem c22_one (ω : Kˣ) (S₁ S₂ : Finset (Fin 6)) (hc₁ : S₁.card = 2)
    (hc₂ : S₂.card = 2) : c22 ω S₁ S₂ hc₁ hc₂ 1 = c2 ω S₂ hc₂ := by
  simp [c22]

private theorem c22_pow (ω : Kˣ) (S₁ S₂ : Finset (Fin 6)) (hc₁ : S₁.card = 2)
    (hc₂ : S₂.card = 2) (hω3 : ω ^ 3 = 1) : ∀ j i, c22 ω S₁ S₂ hc₁ hc₂ j i ^ 3 = 1 := by
  intro j i
  by_cases hj : j = 0
  · subst hj; rw [c22_zero]; exact c2_pow ω S₁ hc₁ hω3 i
  · rw [show c22 ω S₁ S₂ hc₁ hc₂ j = c2 ω S₂ hc₂ from by simp [c22, hj]]
    exact c2_pow ω S₂ hc₂ hω3 i

private theorem c22_prod (ω : Kˣ) (S₁ S₂ : Finset (Fin 6)) (hc₁ : S₁.card = 2)
    (hc₂ : S₂.card = 2) (hω3 : ω ^ 3 = 1) : ∀ j, ∏ i, c22 ω S₁ S₂ hc₁ hc₂ j i = 1 := by
  intro j
  by_cases hj : j = 0
  · subst hj; rw [c22_zero]; exact c2_prod ω S₁ hc₁ hω3
  · rw [show c22 ω S₁ S₂ hc₁ hc₂ j = c2 ω S₂ hc₂ from by simp [c22, hj]]
    exact c2_prod ω S₂ hc₂ hω3

private theorem c22_norm (ω : Kˣ) (S₁ S₂ : Finset (Fin 6)) (hc₁ : S₁.card = 2)
    (hc₂ : S₂.card = 2) (hωq : ω ^ (2 ^ n + 1) = 1) :
    ∀ j i, c22 ω S₁ S₂ hc₁ hc₂ j i ^ (2 ^ n + 1) = 1 := by
  intro j i
  by_cases hj : j = 0
  · subst hj; rw [c22_zero]; exact c2_norm ω S₁ hc₁ hωq i
  · rw [show c22 ω S₁ S₂ hc₁ hc₂ j = c2 ω S₂ hc₂ from by simp [c22, hj]]
    exact c2_norm ω S₂ hc₂ hωq i

private theorem c22_priv (ω : Kˣ) (S₁ S₂ : Finset (Fin 6)) (hc₁ : S₁.card = 2)
    (hc₂ : S₂.card = 2) (hdisj : Disjoint S₁ S₂) (hωo : orderOf ω = 3) :
    ∀ j : Fin 2, ∃ i : Fin 6, (∀ j', j' ≠ j → c22 ω S₁ S₂ hc₁ hc₂ j' i = 1) ∧
      orderOf (c22 ω S₁ S₂ hc₁ hc₂ j i) = 3 := by
  intro j
  have hmem₁ : (↑(S₁.equivFin.symm (Fin.cast hc₁.symm 0)) : Fin 6) ∈ S₁ :=
    (S₁.equivFin.symm (Fin.cast hc₁.symm 0)).2
  have hmem₂ : (↑(S₂.equivFin.symm (Fin.cast hc₂.symm 0)) : Fin 6) ∈ S₂ :=
    (S₂.equivFin.symm (Fin.cast hc₂.symm 0)).2
  by_cases hj : j = 0
  · subst hj
    refine ⟨↑(S₁.equivFin.symm (Fin.cast hc₁.symm 0)), ?_, ?_⟩
    · intro j' hj'
      have hj'1 : j' = 1 := by fin_cases j' <;> simp_all
      subst hj'1
      rw [c22_one]
      exact c2_supp ω S₂ hc₂ (fun h => Finset.disjoint_left.mp hdisj hmem₁ h)
    · rw [c22_zero, c2_eq_gen2_zero ω S₁ hc₁]
      exact hωo
  · have hj1 : j = 1 := by fin_cases j <;> simp_all
    subst hj1
    refine ⟨↑(S₂.equivFin.symm (Fin.cast hc₂.symm 0)), ?_, ?_⟩
    · intro j' hj'
      have hj'0 : j' = 0 := by fin_cases j' <;> simp_all
      subst hj'0
      rw [c22_zero]
      exact c2_supp ω S₁ hc₁ (fun h => Finset.disjoint_left.mp hdisj h hmem₂)
    · rw [c22_one, c2_eq_gen2_zero ω S₂ hc₂]
      exact hωo

private theorem exists_pgroup_le_blockSU_two_two_two (hKd : UnitaryFieldData 2 n K)
    (hpq : 3 ∣ 2 ^ n + 1) {S₁ S₂ : Finset (Fin 6)} (hdisj : Disjoint S₁ S₂)
    (hc₁ : S₁.card = 2) (hc₂ : S₂.card = 2) (hT : S₁ ∪ S₂ ≠ Finset.univ) :
    ∃ P : Subgroup (LargeEvenProj (unitarySU 2 n K 6)), IsPGroup 3 P ∧ ¬ IsCyclic P ∧
      P ≤ (blockSU (n := n) (K := K) S₁ ⊔ blockSU (n := n) (K := K) S₂).map
        (LargeEvenProjMk (unitarySU 2 n K 6)) ∧
      3 ∣ Nat.card ((blockSU (n := n) (K := K) S₁ ⊔ blockSU (n := n) (K := K) S₂).map
        (LargeEvenProjMk (unitarySU 2 n K 6))) := by
  classical
  obtain ⟨ω, hωo, hωq⟩ := CFSG.RankThree.Classical2.exists_orderOf_eq_norm_one hKd
    Nat.prime_three hpq
  have hω3 : ω ^ 3 = 1 := hωo ▸ pow_orderOf_eq_one ω
  set B : Subgroup ↥(unitarySU 2 n K 6) :=
    blockSU (n := n) (K := K) S₁ ⊔ blockSU (n := n) (K := K) S₂ with hB
  have hBle : B ≤ blockSU (n := n) (K := K) (S₁ ∪ S₂) := by
    rw [hB]
    exact sup_le (blockSU_mono Finset.subset_union_left)
      (blockSU_mono Finset.subset_union_right)
  have hθinj : Function.Injective
      (CFSG.RankThree.Classical2.expHom (c22 ω S₁ S₂ hc₁ hc₂)
        (c22_pow ω S₁ S₂ hc₁ hc₂ hω3)) :=
    CFSG.RankThree.Classical2.expHom_injective (c22 ω S₁ S₂ hc₁ hc₂)
      (c22_pow ω S₁ S₂ hc₁ hc₂ hω3) (c22_priv ω S₁ S₂ hc₁ hc₂ hdisj hωo)
  have hmem : ∀ a, diagHom 6 (CFSG.RankThree.Classical2.expHom (c22 ω S₁ S₂ hc₁ hc₂)
      (c22_pow ω S₁ S₂ hc₁ hc₂ hω3) a) ∈ unitarySU 2 n K 6 := fun a =>
    CFSG.RankThree.Classical2.diagHom_expHom_mem_unitarySU hKd (c22 ω S₁ S₂ hc₁ hc₂)
      (c22_pow ω S₁ S₂ hc₁ hc₂ hω3) (c22_prod ω S₁ S₂ hc₁ hc₂ hω3)
      (c22_norm ω S₁ S₂ hc₁ hc₂ hωq) a
  have hmem₀ : diagHom 6 (c2 ω S₁ hc₁) ∈ unitarySU 2 n K 6 :=
    c2_mem_unitary hKd ω S₁ hc₁ hω3 hωq
  have hmem₁ : diagHom 6 (c2 ω S₂ hc₂) ∈ unitarySU 2 n K 6 :=
    c2_mem_unitary hKd ω S₂ hc₂ hω3 hωq
  have hblk : ∀ a, (⟨diagHom 6 (CFSG.RankThree.Classical2.expHom (c22 ω S₁ S₂ hc₁ hc₂)
      (c22_pow ω S₁ S₂ hc₁ hc₂ hω3) a), hmem a⟩ : ↥(unitarySU 2 n K 6)) ∈ B := by
    intro a
    have hfac₀ : (⟨diagHom 6 (c2 ω S₁ hc₁), hmem₀⟩ : ↥(unitarySU 2 n K 6)) ∈
        blockSU (n := n) (K := K) S₁ :=
      diagHom_mem_blockSU_of_supp (fun i hi => c2_supp ω S₁ hc₁ hi) hmem₀
    have hfac₁ : (⟨diagHom 6 (c2 ω S₂ hc₂), hmem₁⟩ : ↥(unitarySU 2 n K 6)) ∈
        blockSU (n := n) (K := K) S₂ :=
      diagHom_mem_blockSU_of_supp (fun i hi => c2_supp ω S₂ hc₂ hi) hmem₁
    have hsplit0 : diagHom 6 (CFSG.RankThree.Classical2.expHom (c22 ω S₁ S₂ hc₁ hc₂)
        (c22_pow ω S₁ S₂ hc₁ hc₂ hω3) a) =
        diagHom 6 (c2 ω S₁ hc₁) ^ (Multiplicative.toAdd a 0).val *
          diagHom 6 (c2 ω S₂ hc₂) ^ (Multiplicative.toAdd a 1).val := by
      rw [show CFSG.RankThree.Classical2.expHom (c22 ω S₁ S₂ hc₁ hc₂)
          (c22_pow ω S₁ S₂ hc₁ hc₂ hω3) a =
          c22 ω S₁ S₂ hc₁ hc₂ 0 ^ (Multiplicative.toAdd a 0).val *
            c22 ω S₁ S₂ hc₁ hc₂ 1 ^ (Multiplicative.toAdd a 1).val from by
        funext i
        simp only [CFSG.RankThree.Classical2.expHom_apply, Fin.prod_univ_two, Pi.mul_apply,
          Pi.pow_apply]]
      rw [map_mul, map_pow, map_pow, c22_zero, c22_one]
    have hsplit : (⟨diagHom 6 (CFSG.RankThree.Classical2.expHom (c22 ω S₁ S₂ hc₁ hc₂)
        (c22_pow ω S₁ S₂ hc₁ hc₂ hω3) a), hmem a⟩ : ↥(unitarySU 2 n K 6)) =
        (⟨diagHom 6 (c2 ω S₁ hc₁), hmem₀⟩ : ↥(unitarySU 2 n K 6)) ^ (Multiplicative.toAdd a 0).val *
        (⟨diagHom 6 (c2 ω S₂ hc₂), hmem₁⟩ : ↥(unitarySU 2 n K 6)) ^
          (Multiplicative.toAdd a 1).val := by
      apply Subtype.ext
      simpa only [Subgroup.coe_mul, Subgroup.coe_pow] using hsplit0
    rw [hsplit, hB]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_sup_left hfac₀) _)
      (Subgroup.pow_mem _ (Subgroup.mem_sup_right hfac₁) _)
  exact exists_pgroup_le_blockSU hKd hT hBle hθinj hmem hblk

private theorem card_level_le_three_of_shapeBad {τ : Fin 6 → Kˣ} (hτ : ShapeBad τ) :
    ∀ (i : Fin 6) (S : Finset (Fin 6)), (∀ j, j ∈ S ↔ τ j = τ i) → S.card ≤ 3 := by
  intro i S hS
  rcases hτ with ⟨v₁, v₂, S₁, S₂, hv, hS₁, hS₂, hc₁, hc₂⟩ |
    ⟨v₁, v₂, v₃, S₁, S₂, S₃, hv₁₂, hv₁₃, hv₂₃, hS₁, hS₂, hS₃, hc₁, hc₂, hc₃⟩
  · have hdisj : Disjoint S₁ S₂ := by
      rw [Finset.disjoint_left]
      intro j hj₁ hj₂
      exact hv (((hS₁ j).mp hj₁).symm.trans ((hS₂ j).mp hj₂))
    have hcard : (S₁ ∪ S₂).card = 6 := by
      rw [Finset.card_union_of_disjoint hdisj, hc₁, hc₂]
    have huniv : S₁ ∪ S₂ = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [hcard]; simp)
    have hi : i ∈ S₁ ∪ S₂ := by rw [huniv]; exact Finset.mem_univ i
    rw [Finset.mem_union] at hi
    have hSe : S = S₁ ∨ S = S₂ := by
      rcases hi with hi | hi
      · left
        ext j
        rw [hS j, hS₁ j, hS₁ i |>.mp hi]
      · right
        ext j
        rw [hS j, hS₂ j, hS₂ i |>.mp hi]
    rcases hSe with rfl | rfl <;> omega
  · have hdisj₁₂ : Disjoint S₁ S₂ := by
      rw [Finset.disjoint_left]
      intro j hj₁ hj₂
      exact hv₁₂ (((hS₁ j).mp hj₁).symm.trans ((hS₂ j).mp hj₂))
    have hdisj₁₃ : Disjoint S₁ S₃ := by
      rw [Finset.disjoint_left]
      intro j hj₁ hj₃
      exact hv₁₃ (((hS₁ j).mp hj₁).symm.trans ((hS₃ j).mp hj₃))
    have hdisj₂₃ : Disjoint S₂ S₃ := by
      rw [Finset.disjoint_left]
      intro j hj₂ hj₃
      exact hv₂₃ (((hS₂ j).mp hj₂).symm.trans ((hS₃ j).mp hj₃))
    have hcard : (S₁ ∪ S₂ ∪ S₃).card = 6 := by
      rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint hdisj₁₂, hc₁, hc₂, hc₃]
      rw [Finset.disjoint_left]
      intro j hj hj₃
      rw [Finset.mem_union] at hj
      rcases hj with hj | hj
      · exact (Finset.disjoint_left.mp hdisj₁₃) hj hj₃
      · exact (Finset.disjoint_left.mp hdisj₂₃) hj hj₃
    have huniv : S₁ ∪ S₂ ∪ S₃ = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [hcard]; simp)
    have hi : i ∈ S₁ ∪ S₂ ∪ S₃ := by rw [huniv]; exact Finset.mem_univ i
    rw [Finset.mem_union, Finset.mem_union] at hi
    have hSe : S = S₁ ∨ S = S₂ ∨ S = S₃ := by
      rcases hi with (hi | hi) | hi
      · left
        ext j
        rw [hS j, hS₁ j, hS₁ i |>.mp hi]
      · right; left
        ext j
        rw [hS j, hS₂ j, hS₂ i |>.mp hi]
      · right; right
        ext j
        rw [hS j, hS₃ j, hS₃ i |>.mp hi]
    rcases hSe with rfl | rfl | rfl <;> omega

private theorem not_isComponentOf_one (hKd : UnitaryFieldData 2 1 K) {τ : Fin 6 → Kˣ}
    (hD : diagHom 6 τ ∈ Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K)))
    (hb : ∀ (i : Fin 6) (S : Finset (Fin 6)), (∀ j, j ∈ S ↔ τ j = τ i) → S.card ≤ 3) :
    ∀ Jb : Subgroup (LargeEvenProj (unitarySU 2 1 K 6)),
      ¬ IsComponentOf Jb (ggFix (TableB.projConj (unitarySU 2 1 K 6) ⟨diagHom 6 τ, hD⟩)) := by
  classical
  haveI : Finite K := hKd.finite
  intro Jb hE
  set ē : GL (Fin 6) K ⧸ LargeEvenScalars (Fin 6) K := QuotientGroup.mk (diagHom 6 τ) with hē
  have hJ := isComponentOf_map_of_injective (Line63.H5.reducedToPGL K 1 6)
    Line63.H5.reducedToPGL_injective hE
  rw [Line63.H5.map_ggFix_eq hD] at hJ
  have hδ : ∀ e ∈ ({ē} : Set (GL (Fin 6) K ⧸ LargeEvenScalars (Fin 6) K)),
      (e, diagHom (5 + 1) ((fun _ => τ) e)) ∈ SUTorus.suPairs (Line63.H5.suToPGL K 1 6) := by
    intro e he
    rw [Set.mem_singleton_iff] at he
    subst he
    refine ⟨hD, fun u v huv => ?_⟩
    show QuotientGroup.mk (diagHom 6 τ) * QuotientGroup.mk (u : GL (Fin 6) K) *
      (QuotientGroup.mk (diagHom 6 τ))⁻¹ = QuotientGroup.mk (v : GL (Fin 6) K)
    rw [huv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  obtain ⟨i, hi⟩ := SUTorus.exists_le_map_blockSU (m := 5) hKd Nat.prime_three (by norm_num)
    (Line63.H5.ker_suToPGL_le_center) hδ hJ
  have hcls : (LinTorus.diagClass {ē} (fun _ => τ) i).card ≤ 3 :=
    hb i _ fun j => by simp [LinTorus.mem_diagClass]
  have hcls1 : 1 ≤ (LinTorus.diagClass {ē} (fun _ => τ) i).card :=
    Finset.card_pos.mpr ⟨i, LinTorus.self_mem_diagClass _ _ i⟩
  haveI hBs : Group.IsSolvable ↥((TableBUE.blockSU (K := K) (n := 1)
      (LinTorus.diagClass {ē} (fun _ => τ) i)).map (Line63.H5.suToPGL K 1 6)) :=
    WitSU.isSolvable_map_blockSU_two_one hKd (Line63.H5.suToPGL K 1 6) hcls1 hcls
  exact Line63.H5.isQuasisimple_not_isSolvable hJ.2.2
    (solvable_of_solvable_injective (Subgroup.inclusion_injective hi))

private theorem three_dvd_card_map_blockSU_two (hKd : UnitaryFieldData 2 n K)
    (hpq : 3 ∣ 2 ^ n + 1) {S : Finset (Fin 6)} (hS : S.card = 2) :
    3 ∣ Nat.card ↥((blockSU (n := n) (K := K) S).map
      (LargeEvenProjMk (unitarySU 2 n K 6))) := by
  classical
  obtain ⟨ω, hωo, hωq⟩ := CFSG.RankThree.Classical2.exists_orderOf_eq_norm_one hKd
    Nat.prime_three hpq
  have hω3 : ω ^ 3 = 1 := hωo ▸ pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hωo
    exact Nat.prime_three.ne_one hωo.symm
  have hmem : diagHom 6 (c2 ω S hS) ∈ unitarySU 2 n K 6 :=
    c2_mem_unitary hKd ω S hS hω3 hωq
  have hblk : (⟨diagHom 6 (c2 ω S hS), hmem⟩ : ↥(unitarySU 2 n K 6)) ∈
      blockSU (n := n) (K := K) S :=
    diagHom_mem_blockSU_of_supp (fun i hi => c2_supp ω S hS hi) hmem
  have hSne : S ≠ Finset.univ := by
    intro h
    have hc := congrArg Finset.card h
    rw [hS] at hc
    simp at hc
  have hd : (⟨diagHom 6 (c2 ω S hS), hmem⟩ : ↥(unitarySU 2 n K 6)) ^ 3 = 1 := by
    apply Subtype.ext
    show (diagHom 6 (c2 ω S hS)) ^ 3 = 1
    rw [← map_pow, show c2 ω S hS ^ 3 = 1 from funext fun i => c2_pow ω S hS hω3 i,
      map_one]
  have hxne : LargeEvenProjMk (unitarySU 2 n K 6)
      (⟨diagHom 6 (c2 ω S hS), hmem⟩ : ↥(unitarySU 2 n K 6)) ≠ 1 := by
    intro h
    have h1 : (⟨diagHom 6 (c2 ω S hS), hmem⟩ : ↥(unitarySU 2 n K 6)) = 1 :=
      mk_eq_one_of_mem_blockSU hSne hblk h
    have h2 : diagHom 6 (c2 ω S hS) = 1 := congrArg Subtype.val h1
    have h3 : c2 ω S hS = 1 := diagHom_injective 6 (by simpa using h2)
    have h4 : c2 ω S hS (↑(S.equivFin.symm (Fin.cast hS.symm 0))) = 1 := by rw [h3]; rfl
    rw [c2_eq_gen2_zero ω S hS] at h4
    exact hω1 h4
  set x : ↥((blockSU (n := n) (K := K) S).map (LargeEvenProjMk (unitarySU 2 n K 6))) :=
    ⟨LargeEvenProjMk (unitarySU 2 n K 6) ⟨diagHom 6 (c2 ω S hS), hmem⟩,
      Subgroup.mem_map.mpr ⟨_, hblk, rfl⟩⟩ with hx
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, hx]
    rw [← map_pow, hd, map_one]
  have hx1 : x ≠ 1 := fun h => hxne (Subtype.ext_iff.mp h)
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hdvd : Nat.card ↥(Subgroup.zpowers x) ∣
      Nat.card ↥((blockSU (n := n) (K := K) S).map
        (LargeEvenProjMk (unitarySU 2 n K 6))) :=
    Subgroup.card_subgroup_dvd_card _
  rwa [Nat.card_zpowers, hord] at hdvd

private theorem le_join_components {R : Type*} [Group R] {Q : Subgroup R → Prop} {B : Subgroup R}
    (hB : Q B) : B ≤ ⨆ (B' : Subgroup R) (_ : Q B'), B' :=
  le_iSup₂ (f := fun B' (_ : Q B') => B') B hB

theorem shapeBad_comp_hyp (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1) {τ : Fin 6 → Kˣ}
    (hτ : ShapeBad τ)
    (hD : diagHom 6 τ ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) :
    ∀ Jb : Subgroup (LargeEvenProj (unitarySU 2 n K 6)),
      IsComponentOf Jb (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨diagHom 6 τ, hD⟩)) →
      ∃ P : Subgroup (LargeEvenProj (unitarySU 2 n K 6)), IsPGroup 3 P ∧ ¬ IsCyclic P ∧
        P ≤ ⨆ (B : Subgroup (LargeEvenProj (unitarySU 2 n K 6)))
          (_ : IsComponentOf B
              (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨diagHom 6 τ, hD⟩)) ∧ B ≠ Jb ∧
            3 ∣ Nat.card B), B := by
  intro Jb hJb
  by_cases hn1 : n = 1
  · subst hn1
    exact absurd hJb (not_isComponentOf_one hKd hD (card_level_le_three_of_shapeBad hτ) Jb)
  · have hn2 : 2 ≤ n := by
      have := hKd.one_le
      omega
    let Q : Subgroup (LargeEvenProj (unitarySU 2 n K 6)) → Prop :=
      fun B => IsComponentOf B
          (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨diagHom 6 τ, hD⟩)) ∧ B ≠ Jb ∧
        3 ∣ Nat.card B
    change ∃ P : Subgroup (LargeEvenProj (unitarySU 2 n K 6)),
      IsPGroup 3 P ∧ ¬ IsCyclic P ∧
        P ≤ ⨆ (B : Subgroup (LargeEvenProj (unitarySU 2 n K 6))) (_ : Q B), B
    rcases hτ with h33 | h222
    · rcases h33 with ⟨v₁, v₂, S₁, S₂, hv, hS₁, hS₂, hc₁, hc₂⟩
      have hS₁ne : S₁ ≠ Finset.univ := by
        intro h
        have hc := congrArg Finset.card h
        rw [hc₁] at hc
        simp at hc
      have hS₂ne : S₂ ≠ Finset.univ := by
        intro h
        have hc := congrArg Finset.card h
        rw [hc₂] at hc
        simp at hc
      have hdisj : Disjoint S₁ S₂ := by
        rw [Finset.disjoint_left]
        intro i hi₁ hi₂
        exact hv (((hS₁ i).mp hi₁).symm.trans ((hS₂ i).mp hi₂))
      have hcomp₁ : IsComponentOf
          ((blockSU (n := n) (K := K) S₁).map (LargeEvenProjMk (unitarySU 2 n K 6)))
          (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨diagHom 6 τ, hD⟩)) := by
        exact Line63.H5.isComponentOf_map_blockSU_of_level hKd hn2 hD rfl hS₁
          (by omega)
      have hcomp₂ : IsComponentOf
          ((blockSU (n := n) (K := K) S₂).map (LargeEvenProjMk (unitarySU 2 n K 6)))
          (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨diagHom 6 τ, hD⟩)) := by
        exact Line63.H5.isComponentOf_map_blockSU_of_level hKd hn2 hD rfl hS₂
          (by omega)
      have hcomm : ∀ a ∈ (blockSU (n := n) (K := K) S₁).map (LargeEvenProjMk (unitarySU 2 n K 6)),
          ∀ b ∈ (blockSU (n := n) (K := K) S₂).map
            (LargeEvenProjMk (unitarySU 2 n K 6)), a * b = b * a := by
        intro a ha b hb
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
        rw [← map_mul, ← map_mul, Line63.H5.blockSU_commute_of_disjoint hdisj hx hy]
      have hBne : (blockSU (n := n) (K := K) S₁).map (LargeEvenProjMk (unitarySU 2 n K 6)) ≠
          (blockSU (n := n) (K := K) S₂).map (LargeEvenProjMk (unitarySU 2 n K 6)) := by
        intro heq
        apply Line63.H5.isQuasisimple_not_comm hcomp₁.2.2
        intro a b
        exact Subtype.ext (hcomm a a.2 b (heq ▸ b.2))
      by_cases h1 : (blockSU (n := n) (K := K) S₁).map (LargeEvenProjMk (unitarySU 2 n K 6)) = Jb
      · have h2 : (blockSU (n := n) (K := K) S₂).map (LargeEvenProjMk (unitarySU 2 n K 6)) ≠ Jb :=
          fun h => hBne (h1.trans h.symm)
        obtain ⟨P, hP3, hPnc, hPle, hBdiv⟩ := exists_pgroup_le_blockSU_three hKd hpq hc₂ hS₂ne
        exact ⟨P, hP3, hPnc,
          hPle.trans (le_join_components (Q := Q) (show Q _ from ⟨hcomp₂, h2, hBdiv⟩))⟩
      · obtain ⟨P, hP3, hPnc, hPle, hBdiv⟩ := exists_pgroup_le_blockSU_three hKd hpq hc₁ hS₁ne
        exact ⟨P, hP3, hPnc,
          hPle.trans (le_join_components (Q := Q) (show Q _ from ⟨hcomp₁, h1, hBdiv⟩))⟩
    · rcases h222 with ⟨v₁, v₂, v₃, S₁, S₂, S₃, hv₁₂, hv₁₃, hv₂₃, hS₁, hS₂, hS₃,
        hc₁, hc₂, hc₃⟩
      have hdisj₁₂ : Disjoint S₁ S₂ := by
        rw [Finset.disjoint_left]
        intro i hi₁ hi₂
        exact hv₁₂ (((hS₁ i).mp hi₁).symm.trans ((hS₂ i).mp hi₂))
      have hdisj₁₃ : Disjoint S₁ S₃ := by
        rw [Finset.disjoint_left]
        intro i hi₁ hi₃
        exact hv₁₃ (((hS₁ i).mp hi₁).symm.trans ((hS₃ i).mp hi₃))
      have hdisj₂₃ : Disjoint S₂ S₃ := by
        rw [Finset.disjoint_left]
        intro i hi₂ hi₃
        exact hv₂₃ (((hS₂ i).mp hi₂).symm.trans ((hS₃ i).mp hi₃))
      have hcomp₁ : IsComponentOf ((blockSU (n := n) (K := K) S₁).map
          (LargeEvenProjMk (unitarySU 2 n K 6)))
          (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨diagHom 6 τ, hD⟩)) :=
        Line63.H5.isComponentOf_map_blockSU_of_level hKd hn2 hD rfl hS₁ (by omega)
      have hcomp₂ : IsComponentOf ((blockSU (n := n) (K := K) S₂).map
          (LargeEvenProjMk (unitarySU 2 n K 6)))
          (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨diagHom 6 τ, hD⟩)) :=
        Line63.H5.isComponentOf_map_blockSU_of_level hKd hn2 hD rfl hS₂ (by omega)
      have hcomp₃ : IsComponentOf ((blockSU (n := n) (K := K) S₃).map
          (LargeEvenProjMk (unitarySU 2 n K 6)))
          (ggFix (TableB.projConj (unitarySU 2 n K 6) ⟨diagHom 6 τ, hD⟩)) :=
        Line63.H5.isComponentOf_map_blockSU_of_level hKd hn2 hD rfl hS₃ (by omega)
      have hdiv₁ : 3 ∣ Nat.card ((blockSU (n := n) (K := K) S₁).map
          (LargeEvenProjMk (unitarySU 2 n K 6))) :=
        three_dvd_card_map_blockSU_two hKd hpq hc₁
      have hdiv₂ : 3 ∣ Nat.card ((blockSU (n := n) (K := K) S₂).map
          (LargeEvenProjMk (unitarySU 2 n K 6))) :=
        three_dvd_card_map_blockSU_two hKd hpq hc₂
      have hdiv₃ : 3 ∣ Nat.card ((blockSU (n := n) (K := K) S₃).map
          (LargeEvenProjMk (unitarySU 2 n K 6))) :=
        three_dvd_card_map_blockSU_two hKd hpq hc₃
      have hcomm₁₂ : ∀ a ∈ (blockSU (n := n) (K := K) S₁).map
            (LargeEvenProjMk (unitarySU 2 n K 6)),
          ∀ b ∈ (blockSU (n := n) (K := K) S₂).map
            (LargeEvenProjMk (unitarySU 2 n K 6)), a * b = b * a := by
        intro a ha b hb
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
        rw [← map_mul, ← map_mul, Line63.H5.blockSU_commute_of_disjoint hdisj₁₂ hx hy]
      have hcomm₁₃ : ∀ a ∈ (blockSU (n := n) (K := K) S₁).map
            (LargeEvenProjMk (unitarySU 2 n K 6)),
          ∀ b ∈ (blockSU (n := n) (K := K) S₃).map
            (LargeEvenProjMk (unitarySU 2 n K 6)), a * b = b * a := by
        intro a ha b hb
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
        rw [← map_mul, ← map_mul, Line63.H5.blockSU_commute_of_disjoint hdisj₁₃ hx hy]
      have hcomm₂₃ : ∀ a ∈ (blockSU (n := n) (K := K) S₂).map
            (LargeEvenProjMk (unitarySU 2 n K 6)),
          ∀ b ∈ (blockSU (n := n) (K := K) S₃).map
            (LargeEvenProjMk (unitarySU 2 n K 6)), a * b = b * a := by
        intro a ha b hb
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
        rw [← map_mul, ← map_mul, Line63.H5.blockSU_commute_of_disjoint hdisj₂₃ hx hy]
      have hCne₁₂ : (blockSU (n := n) (K := K) S₁).map
            (LargeEvenProjMk (unitarySU 2 n K 6)) ≠
          (blockSU (n := n) (K := K) S₂).map (LargeEvenProjMk (unitarySU 2 n K 6)) := by
        intro heq
        apply Line63.H5.isQuasisimple_not_comm hcomp₁.2.2
        intro a b
        exact Subtype.ext (hcomm₁₂ a a.2 b (heq ▸ b.2))
      have hCne₁₃ : (blockSU (n := n) (K := K) S₁).map
            (LargeEvenProjMk (unitarySU 2 n K 6)) ≠
          (blockSU (n := n) (K := K) S₃).map (LargeEvenProjMk (unitarySU 2 n K 6)) := by
        intro heq
        apply Line63.H5.isQuasisimple_not_comm hcomp₁.2.2
        intro a b
        exact Subtype.ext (hcomm₁₃ a a.2 b (heq ▸ b.2))
      have hCne₂₃ : (blockSU (n := n) (K := K) S₂).map
            (LargeEvenProjMk (unitarySU 2 n K 6)) ≠
          (blockSU (n := n) (K := K) S₃).map (LargeEvenProjMk (unitarySU 2 n K 6)) := by
        intro heq
        apply Line63.H5.isQuasisimple_not_comm hcomp₂.2.2
        intro a b
        exact Subtype.ext (hcomm₂₃ a a.2 b (heq ▸ b.2))
      have hT₁₂ : S₁ ∪ S₂ ≠ Finset.univ := by
        intro h
        have hc := congrArg Finset.card h
        rw [Finset.card_union_of_disjoint hdisj₁₂, hc₁, hc₂] at hc
        simp at hc
      have hT₁₃ : S₁ ∪ S₃ ≠ Finset.univ := by
        intro h
        have hc := congrArg Finset.card h
        rw [Finset.card_union_of_disjoint hdisj₁₃, hc₁, hc₃] at hc
        simp at hc
      have hT₂₃ : S₂ ∪ S₃ ≠ Finset.univ := by
        intro h
        have hc := congrArg Finset.card h
        rw [Finset.card_union_of_disjoint hdisj₂₃, hc₂, hc₃] at hc
        simp at hc
      by_cases h1 : (blockSU (n := n) (K := K) S₁).map
          (LargeEvenProjMk (unitarySU 2 n K 6)) = Jb
      · have h2 : (blockSU (n := n) (K := K) S₂).map
            (LargeEvenProjMk (unitarySU 2 n K 6)) ≠ Jb :=
          fun h => hCne₁₂ (h1.trans h.symm)
        have h3 : (blockSU (n := n) (K := K) S₃).map
            (LargeEvenProjMk (unitarySU 2 n K 6)) ≠ Jb :=
          fun h => hCne₁₃ (h1.trans h.symm)
        obtain ⟨P, hP3, hPnc, hPle, _⟩ :=
          exists_pgroup_le_blockSU_two_two_two hKd hpq hdisj₂₃ hc₂ hc₃ hT₂₃
        have hjoin : (blockSU (n := n) (K := K) S₂).map
              (LargeEvenProjMk (unitarySU 2 n K 6)) ⊔
            (blockSU (n := n) (K := K) S₃).map (LargeEvenProjMk (unitarySU 2 n K 6)) ≤
            ⨆ (B) (_ : Q B), B :=
          sup_le (le_join_components (Q := Q) (show Q _ from ⟨hcomp₂, h2, hdiv₂⟩))
            (le_join_components (Q := Q) (show Q _ from ⟨hcomp₃, h3, hdiv₃⟩))
        rw [Subgroup.map_sup] at hPle
        exact ⟨P, hP3, hPnc, hPle.trans hjoin⟩
      · by_cases h2 : (blockSU (n := n) (K := K) S₂).map
            (LargeEvenProjMk (unitarySU 2 n K 6)) = Jb
        · have h3 : (blockSU (n := n) (K := K) S₃).map
              (LargeEvenProjMk (unitarySU 2 n K 6)) ≠ Jb :=
            fun h => hCne₂₃ (h2.trans h.symm)
          obtain ⟨P, hP3, hPnc, hPle, _⟩ :=
            exists_pgroup_le_blockSU_two_two_two hKd hpq hdisj₁₃ hc₁ hc₃ hT₁₃
          have hjoin : (blockSU (n := n) (K := K) S₁).map
                (LargeEvenProjMk (unitarySU 2 n K 6)) ⊔
              (blockSU (n := n) (K := K) S₃).map (LargeEvenProjMk (unitarySU 2 n K 6)) ≤
              ⨆ (B) (_ : Q B), B :=
            sup_le (le_join_components (Q := Q) (show Q _ from ⟨hcomp₁, h1, hdiv₁⟩))
              (le_join_components (Q := Q) (show Q _ from ⟨hcomp₃, h3, hdiv₃⟩))
          rw [Subgroup.map_sup] at hPle
          exact ⟨P, hP3, hPnc, hPle.trans hjoin⟩
        · obtain ⟨P, hP3, hPnc, hPle, _⟩ :=
            exists_pgroup_le_blockSU_two_two_two hKd hpq hdisj₁₂ hc₁ hc₂ hT₁₂
          have hjoin : (blockSU (n := n) (K := K) S₁).map
                (LargeEvenProjMk (unitarySU 2 n K 6)) ⊔
              (blockSU (n := n) (K := K) S₂).map (LargeEvenProjMk (unitarySU 2 n K 6)) ≤
              ⨆ (B) (_ : Q B), B :=
            sup_le (le_join_components (Q := Q) (show Q _ from ⟨hcomp₁, h1, hdiv₁⟩))
              (le_join_components (Q := Q) (show Q _ from ⟨hcomp₂, h2, hdiv₂⟩))
          rw [Subgroup.map_sup] at hPle
          exact ⟨P, hP3, hPnc, hPle.trans hjoin⟩

theorem not_ggFixCompCyclic_of_shapeBad (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* LargeEvenProj (unitarySU 2 n K 6)}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') {M : GL (Fin 6) K}
    (hM : M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)))
    (hsh : ShapeBadMat hKd M) {a : MulAut L'}
    (hc : ∀ l, TableB.projConj (unitarySU 2 n K 6) ⟨M, hM⟩ (ψ l) = ψ (a l)) :
    ¬ GGFixCompCyclic 3 a := by
  obtain ⟨P, hP, τ, hMP, hτ⟩ := hsh
  have hPN : P ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
    TableBUE.gu_subset_normalizer hKd
      (TableBUD.mem_guSet_of_mem_primeFormUnitary hKd hP)
  have hDN : P⁻¹ * M * P ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hPN) hM) hPN
  have hD : diagHom 6 τ ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
    hMP ▸ hDN
  let θ := TableBUE.conjProj hKd P hP
  let ψ'' : L' →* LargeEvenProj (unitarySU 2 n K 6) := θ.toMonoidHom.comp ψ
  have hψ'' : Function.Surjective ψ'' := θ.surjective.comp hψ
  have hker'' : ψ''.ker ≤ Subgroup.center L' := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact θ.injective (by rw [show θ (ψ x) = 1 from hx, map_one])
  have hsub : (⟨diagHom 6 τ, hD⟩ : ↥(Subgroup.normalizer (unitarySU 2 n K 6 :
      Set (GL (Fin 6) K)))) = ⟨P⁻¹ * M * P, hDN⟩ := Subtype.ext hMP.symm
  have hc'' : ∀ l, TableB.projConj (unitarySU 2 n K 6) ⟨diagHom 6 τ, hD⟩ (ψ'' l) =
      ψ'' (a l) := by
    intro l
    have htw := TableBUD.conjProj_projConj hKd P hP ⟨M, hM⟩ hDN (ψ l)
    rw [hc l] at htw
    rw [hsub]
    exact htw.symm
  exact not_ggFixCompCyclic_of_comp hψ'' hker'' hc''
    (shapeBad_comp_hyp hKd hpq hτ hD)

end CFSG.StandardType.UnitSixThreeKG

end
