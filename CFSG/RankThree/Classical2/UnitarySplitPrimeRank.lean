module

public import CFSG.RankThree.Classical2.CentralLiftCommutator
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.RankThree.Classical.OrthogonalOrderThree
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.LocalAnalysis.RankThreeEvenClassification.InvolutionLocal
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.Classical2

open scoped commutatorElement
open Matrix CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.SectionRank.OddCover CFSG.RankThree.Classical

section Elementary

variable {Y T : Type*} [Group Y] [Group T] {φ : Y →* T}

theorem exists_elemAbelian_le_centralizer [Finite Y] (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {D : Subgroup T}
    (hDp : ∀ x ∈ D, x ^ p = 1) (hF : ∀ x ∈ D.comap φ, ∀ y ∈ D.comap φ, x * y = y * x)
    {r : ℕ} (hr : p ^ r ≤ Nat.card D) {u : Y} (hu : u ^ 2 = 1)
    (huD : ∀ x ∈ D, Commute (φ u) x) :
    ∃ V : Subgroup Y, V ≤ D.comap φ ∧ IsElemAbelian p V ∧ Nat.card V = p ^ r ∧
      V ≤ Subgroup.centralizer {u} := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set F := D.comap φ with hFdef
  let Fp : Subgroup Y :=
    { carrier := {x | x ∈ F ∧ x ^ p = 1}
      mul_mem' := fun {x y} hx hy => ⟨F.mul_mem hx.1 hy.1, by
        rw [(show Commute x y from hF x hx.1 y hy.1).mul_pow, hx.2, hy.2, one_mul]⟩
      one_mem' := ⟨F.one_mem, one_pow p⟩
      inv_mem' := fun {x} hx => ⟨F.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hFpF : Fp ≤ F := fun x hx => hx.1
  have hcard : Nat.card D ≤ Nat.card Fp := by
    let ψ : F →* T := φ.comp F.subtype
    have hψ : ψ.range = D := by
      ext t
      constructor
      · rintro ⟨x, rfl⟩
        exact x.2
      · intro ht
        obtain ⟨y, rfl⟩ := hφ t
        exact ⟨⟨y, ht⟩, rfl⟩
    let pw : F →* F :=
      { toFun := fun x => x ^ p
        map_one' := one_pow p
        map_mul' := fun x y =>
          (show Commute x y from Subtype.ext (hF x x.2 y y.2)).mul_pow p }
    have hle : pw.range ≤ ψ.ker := by
      rintro _ ⟨x, rfl⟩
      rw [MonoidHom.mem_ker]
      change φ ((x : Y) ^ p) = 1
      rw [map_pow]
      exact hDp _ x.2
    have hpwker : pw.ker = Fp.subgroupOf F := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      change x ^ p = 1 ↔ (x : Y) ∈ F ∧ (x : Y) ^ p = 1
      rw [← Subgroup.coe_pow, ← OneMemClass.coe_one F, Subtype.ext_iff]
      exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
    have hker' : Nat.card pw.ker = Nat.card Fp := by
      rw [hpwker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFpF).toEquiv
    have h1 : Nat.card D = ψ.ker.index := by rw [Subgroup.index_ker, hψ]
    have h2 : ψ.ker.index ≤ pw.range.index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.index_dvd_of_le hle)
    have h3 : Nat.card pw.ker * Nat.card pw.range = Nat.card F := by
      rw [← Subgroup.index_ker pw, Subgroup.card_mul_index]
    have h4 : Nat.card pw.range * pw.range.index = Nat.card F := Subgroup.card_mul_index _
    have h5 : pw.range.index = Nat.card pw.ker := by
      have hpos : 0 < Nat.card pw.range := Nat.card_pos
      refine Nat.eq_of_mul_eq_mul_left hpos ?_
      rw [h4, ← h3, mul_comm]
    rw [h1, ← hker']
    exact h2.trans h5.le
  have hFpP : IsPGroup p Fp := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact x.2.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hFpP
  have hrk : r ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hr.trans (hcard.trans hk.le))
  obtain ⟨V₀, hV₀⟩ := Sylow.exists_subgroup_card_pow_prime p
    (show p ^ r ∣ Nat.card Fp by rw [hk]; exact pow_dvd_pow p hrk)
  set V := V₀.map Fp.subtype with hVdef
  have hVFp : V ≤ Fp := Subgroup.map_subtype_le V₀
  have hcent : ∀ x ∈ Fp, x * u = u * x := by
    intro x hx
    have hc : ⁅u, x⁆ ∈ Subgroup.center Y :=
      hker (commutatorElement_mem_ker φ (huD _ hx.1))
    have hc2 : ⁅u, x⁆ ^ 2 = 1 := by
      have h := CFSG.SectionRank.OddCover.commutatorElement_mul_left_of_mem_center
        (a := u) hc
      rw [← pow_two, hu, commutatorElement_one_left] at h
      rw [pow_two]
      exact h.symm
    have hcpow : ∀ j : ℕ, ⁅u, x ^ j⁆ = ⁅u, x⁆ ^ j := by
      intro j
      induction j with
      | zero => rw [pow_zero, pow_zero, commutatorElement_one_right]
      | succ j ih =>
        rw [pow_succ, CFSG.SectionRank.OddCover.commutatorElement_mul_right_of_mem_center hc,
          ih, pow_succ]
    have hcp : ⁅u, x⁆ ^ p = 1 := by
      rw [← hcpow p, hx.2, commutatorElement_one_right]
    have h1 := eq_one_of_sq_eq_one_of_pow_eq_one (hp.odd_of_ne_two hp2) hc2 hcp
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  refine ⟨V, hVFp.trans hFpF, ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => (hVFp hx).2⟩, ?_, ?_⟩
  · exact hF _ (hFpF (hVFp a.2)) _ (hFpF (hVFp b.2))
  · rw [hVdef, Subgroup.card_map_of_injective Fp.subtype_injective, hV₀]
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcent x (hVFp hx)

theorem exists_involution_elemAbelian_of_cover {G : Type*} [Group G] [Finite G] (Y : Subgroup G)
    {T : Type*} [Group T] {φ : Y →* T} (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {D : Subgroup T}
    (hDp : ∀ x ∈ D, x ^ p = 1) (hF : ∀ x ∈ D.comap φ, ∀ y ∈ D.comap φ, x * y = y * x)
    {r : ℕ} (hr : p ^ r ≤ Nat.card D) {z : T} (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1)
    (hzD : ∀ x ∈ D, Commute z x) :
    ∃ u : G, u ∈ Y ∧ orderOf u = 2 ∧ ∃ V : Subgroup G, V ≤ Y ⊓ Subgroup.centralizer {u} ∧
      IsElemAbelian p V ∧ Nat.card V = p ^ r := by
  obtain ⟨y, hy⟩ := hφ z
  have hoz : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hdvd : 2 ∣ orderOf y := by
    rw [← hoz, ← hy]
    exact orderOf_map_dvd φ y
  have hy0 : orderOf y ≠ 0 := (orderOf_pos y).ne'
  set u : Y := y ^ (orderOf y / 2)
  have hu : orderOf u = 2 := orderOf_pow_orderOf_div hy0 hdvd
  have hu2 : u ^ 2 = 1 := by rw [← hu, pow_orderOf_eq_one]
  have huD : ∀ x ∈ D, Commute (φ u) x := fun x hx => by
    rw [map_pow, hy]
    exact (hzD x hx).pow_left _
  obtain ⟨V, -, hVab, hVcard, hVcent⟩ := exists_elemAbelian_le_centralizer hφ hker hp hp2 hDp hF
    hr hu2 huD
  refine ⟨u, u.2, by rw [Subgroup.orderOf_coe, hu], V.map Y.subtype, ?_, ?_, ?_⟩
  · refine le_inf (Subgroup.map_subtype_le V) ?_
    rintro _ ⟨v, hv, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hVcent hv)
    exact congrArg Subtype.val h
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨va, hva, rfl⟩⟩ := a
      obtain ⟨_, ⟨vb, hvb, rfl⟩⟩ := b
      apply Subtype.ext
      change (va : G) * vb = vb * va
      exact congrArg Subtype.val
        (congrArg Subtype.val (hVab.1.is_comm.comm ⟨va, hva⟩ ⟨vb, hvb⟩))
    · rintro _ ⟨v, hv, rfl⟩
      change (v : G) ^ p = 1
      rw [← Subgroup.coe_pow, hVab.2 v hv, OneMemClass.coe_one]
  · rw [Subgroup.card_map_of_injective Y.subtype_injective, hVcard]

theorem le_localRank_of_involution_elemAbelian {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {u : G} (hu : orderOf u = 2) {V : Subgroup G}
    (hVu : V ≤ Subgroup.centralizer {u}) (hVab : IsElemAbelian p V) {r : ℕ}
    (hVcard : Nat.card V = p ^ r) : r ≤ localRank p G := by
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu
    omega
  have hu2 : u ^ 2 = 1 := by rw [← hu, pow_orderOf_eq_one]
  have hloc := CFSG.RankThreeEvenClassification.Helpers.involution_centralizer_isTwoLocal u hu1 hu2
  have h1 := CFSG.SectionRank.le_pRank hp.one_lt hVu hVab hVcard
  exact h1.trans (le_csSup (CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_bddAbove p hp G)
    ⟨_, hloc, rfl⟩)

end Elementary

section Exponent

variable {p : ℕ} [NeZero p]

@[expose] def expHom {J ι : Type*} [Fintype J] {M : Type*} [CommMonoid M] (c : J → ι → M)
    (hc : ∀ j i, c j i ^ p = 1) : Multiplicative (J → ZMod p) →* (ι → M) where
  toFun a := fun i => ∏ j, c j i ^ (Multiplicative.toAdd a j).val
  map_one' := by
    funext i
    simp
  map_mul' a b := by
    funext i
    simp only [toAdd_mul, Pi.add_apply, Pi.mul_apply]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [ZMod.val_add, ← pow_eq_pow_mod _ (hc j i), pow_add]

theorem expHom_apply {J ι : Type*} [Fintype J] {M : Type*} [CommMonoid M] (c : J → ι → M)
    (hc : ∀ j i, c j i ^ p = 1) (a : Multiplicative (J → ZMod p)) (i : ι) :
    expHom c hc a i = ∏ j, c j i ^ (Multiplicative.toAdd a j).val :=
  rfl

theorem expHom_single [Fact (1 < p)] {J ι : Type*} [Fintype J] [DecidableEq J] {M : Type*}
    [CommMonoid M] (c : J → ι → M) (hc : ∀ j i, c j i ^ p = 1) (j : J) :
    expHom c hc (Multiplicative.ofAdd (Pi.single j (1 : ZMod p))) = c j := by
  funext i
  rw [expHom_apply, toAdd_ofAdd]
  rw [Finset.prod_eq_single j]
  · rw [Pi.single_eq_same, ZMod.val_one, pow_one]
  · intro j' _ hj'
    rw [Pi.single_eq_of_ne hj', ZMod.val_zero, pow_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem closure_range_single_eq_top {J : Type*} [Fintype J] [DecidableEq J] :
    AddSubgroup.closure (Set.range fun j : J => Pi.single j (1 : ZMod p)) = ⊤ := by
  refine eq_top_iff.mpr fun a _ => ?_
  rw [← Finset.univ_sum_single a]
  refine AddSubgroup.sum_mem _ fun j _ => ?_
  have h : (Pi.single j (a j) : J → ZMod p) =
      (a j).val • (Pi.single j (1 : ZMod p) : J → ZMod p) := by
    ext k
    rw [Pi.smul_apply, Pi.single_apply, Pi.single_apply]
    split_ifs with hk
    · rw [nsmul_one, ZMod.natCast_zmod_val]
    · rw [smul_zero]
  rw [h]
  exact AddSubgroup.nsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self j)) _

end Exponent

section Monomial

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem diagHom_unitary (hK : UnitaryFieldData ℓ f K) {n : ℕ} {d : Fin n → Kˣ}
    (hd : ∀ i, (d i : K) ^ (ℓ ^ f + 1) = 1) :
    ((diagHom n d : Matrix (Fin n) (Fin n) K).map hK.bar)ᵀ * (diagHom n d : Matrix _ _ K) = 1 := by
  rw [coe_diagHom, diagonal_map (map_zero hK.bar), diagonal_transpose, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1
  funext i
  rw [hK.bar_apply, ← pow_succ, hd i]

theorem permGL_unitary (hK : UnitaryFieldData ℓ f K) {n : ℕ} (π : Equiv.Perm (Fin n)) :
    (((permGL π : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map hK.bar)ᵀ *
      ((permGL π : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply]
  have hmap : ((π⁻¹).permMatrix K).map hK.bar = (π⁻¹).permMatrix K := by
    ext i j
    simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    split_ifs
    · exact map_one hK.bar
    · exact map_zero hK.bar
  rw [hmap, Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, inv_inv, inv_mul_cancel,
    Matrix.permMatrix_one]

theorem unitary_mul (hK : UnitaryFieldData ℓ f K) {n : ℕ} {A B : Matrix (Fin n) (Fin n) K}
    (hA : (A.map hK.bar)ᵀ * A = 1) (hB : (B.map hK.bar)ᵀ * B = 1) :
    ((A * B).map hK.bar)ᵀ * (A * B) = 1 := by
  rw [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ A,
    hA, Matrix.one_mul, hB]

theorem det_permGL {n : ℕ} (π : Equiv.Perm (Fin n)) :
    ((permGL π : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det =
      ((Equiv.Perm.sign π : ℤ) : K) := by
  rw [MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, Matrix.det_permutation,
    Equiv.Perm.sign_inv]

theorem permGL_mul_diagHom_mul_inv {n : ℕ} (π : Equiv.Perm (Fin n)) (d : Fin n → Kˣ) :
    permGL π * diagHom n d * (permGL π)⁻¹ = diagHom n (d ∘ π.symm) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, ← map_inv, MonoidHom.coe_toHomUnits,
    MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, Matrix.permMatrixHom_apply, inv_inv,
    coe_diagHom, coe_diagHom, Equiv.Perm.permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix]
  change (diagonal fun i => (d i : K)).submatrix (⇑π.symm ∘ id) (id ∘ ⇑π.symm) = _
  rw [Function.comp_id, Function.id_comp, Matrix.submatrix_diagonal_equiv]
  rfl

theorem diagHom_commute {n : ℕ} (d d' : Fin n → Kˣ) : Commute (diagHom n d) (diagHom n d') := by
  rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]

end Monomial

section Witness

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem exists_rank_witness {G : Type*} [Group G] [Finite G] (Y : Subgroup G)
    (hK : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n)
    (φ : Y →* unitaryPSU hK n) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) {m : ℕ} (c : Fin m → Fin n → Kˣ)
    (hcp : ∀ j i, c j i ^ p = 1)
    (hcS : ∀ a, diagHom n (@expHom p ⟨hp.ne_zero⟩ _ _ _ _ _ c hcp a) ∈ unitarySU ℓ f K n)
    (hinj : Function.Injective (@expHom p ⟨hp.ne_zero⟩ _ _ _ _ _ c hcp))
    (hswap : ∀ j k, j ≠ k → ∃ w ∈ unitarySU ℓ f K n,
      w * diagHom n (c j) * w⁻¹ = diagHom n (c k) ∧ w * diagHom n (c k) * w⁻¹ = diagHom n (c j))
    {z₀ : GL (Fin n) K} (hz₀S : z₀ ∈ unitarySU ℓ f K n)
    (hz₀sc : ∀ c : Kˣ, z₀ ≠ Matrix.GeneralLinearGroup.scalar (Fin n) c) (hz₀2 : z₀ ^ 2 = 1)
    (hz₀c : ∀ a, Commute z₀ (diagHom n (@expHom p ⟨hp.ne_zero⟩ _ _ _ _ _ c hcp a))) :
    ∃ u : G, u ∈ Y ∧ orderOf u = 2 ∧ ∃ V : Subgroup G, V ≤ Y ⊓ Subgroup.centralizer {u} ∧
      IsElemAbelian p V ∧ Nat.card V = p ^ (m - if p ∣ n then 1 else 0) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Finite K := hK.finite
  set S := unitarySU ℓ f K n
  set E := expHom (p := p) c hcp
  let δ : Multiplicative (Fin m → ZMod p) →* S := ((diagHom n).comp E).codRestrict S hcS
  have hδ : ∀ a, (δ a : GL (Fin n) K) = diagHom n (E a) := fun a => rfl
  let θ : Multiplicative (Fin m → ZMod p) →* unitaryPSU hK n := (unitaryProj hK n).comp δ
  set D := θ.range with hDdef
  have hθsingle : ∀ j, (δ (Multiplicative.ofAdd (Pi.single j 1)) : GL (Fin n) K) =
      diagHom n (c j) := fun j => by rw [hδ, expHom_single]
  have hpow : ∀ a : Multiplicative (Fin m → ZMod p), a ^ p = 1 := by
    intro a
    change Multiplicative.ofAdd (p • Multiplicative.toAdd a) = 1
    have : p • Multiplicative.toAdd a = 0 := by
      funext i
      simp [nsmul_eq_mul]
    rw [this]
    rfl
  have hDp : ∀ x ∈ D, x ^ p = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow, hpow, map_one]
  have hgen : ∀ j k : Fin m, liftComm φ hφ (θ (Multiplicative.ofAdd (Pi.single j 1)))
      (θ (Multiplicative.ofAdd (Pi.single k 1))) = 1 := by
    intro j k
    rcases eq_or_ne j k with rfl | hjk
    · exact liftComm_self hφ _
    obtain ⟨w, hwS, hw1, hw2⟩ := hswap j k hjk
    have hcomm : Commute (θ (Multiplicative.ofAdd (Pi.single j 1)))
        (θ (Multiplicative.ofAdd (Pi.single k 1))) := (Commute.all _ _).map θ
    refine liftComm_eq_one_of_conj_swap hφ hker (hp.odd_of_ne_two hp2) hcomm
      (by rw [← map_pow, hpow, map_one]) (unitaryProj hK n ⟨w, hwS⟩) ?_ ?_
    · change unitaryProj hK n (⟨w, hwS⟩ * δ _ * ⟨w, hwS⟩⁻¹) = unitaryProj hK n (δ _)
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hθsingle, hθsingle, hw1]
    · change unitaryProj hK n (⟨w, hwS⟩ * δ _ * ⟨w, hwS⟩⁻¹) = unitaryProj hK n (δ _)
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hθsingle, hθsingle, hw2]
  have hall : ∀ s ∈ D, ∀ t ∈ D, liftComm φ hφ s t = 1 := by
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
    refine liftComm_eq_one_of_closure hφ hker θ closure_range_single_eq_top ?_ a a'
    rintro _ ⟨j, rfl⟩ _ ⟨k, rfl⟩
    exact hgen j k
  have hF : ∀ x ∈ D.comap φ, ∀ y ∈ D.comap φ, x * y = y * x := fun x hx y hy =>
    mul_comm_of_liftComm_eq_one hφ hker hall hx hy
  have hscalar : ∀ a, θ a = 1 → ∃ c : Kˣ, c ^ n = 1 ∧ c ^ p = 1 ∧
      diagHom n (E a) = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
    intro a ha
    have hmem : δ a ∈ unitaryScalars hK n := by
      rw [← ker_unitaryProj hK n]
      exact ha
    obtain ⟨c, -, hcn, hc⟩ := mem_unitaryScalars.mp hmem
    refine ⟨c, hcn, ?_, by rw [← hδ, hc]⟩
    have h1 : (δ (a ^ p) : GL (Fin n) K) = 1 := by rw [hpow, map_one]; rfl
    rw [map_pow, Subgroup.coe_pow, hc, ← map_pow] at h1
    have hn0 : (⟨0, by omega⟩ : Fin n) = ⟨0, by omega⟩ := rfl
    have h2 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩
      ⟨0, by omega⟩) h1
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq, Units.val_one, Matrix.one_apply_eq] at h2
    exact Units.ext (by simpa using h2)
  have hkercard : Nat.card θ.ker ≤ p ^ (if p ∣ n then 1 else 0) := by
    split_ifs with hpn
    ·
      rw [pow_one]
      let ev : θ.ker →* Kˣ := ((Pi.evalMonoidHom (fun _ : Fin n => Kˣ) ⟨0, by omega⟩).comp E).comp
        θ.ker.subtype
      have hev : Function.Injective ev := by
        refine (injective_iff_map_eq_one ev).mpr fun x hx => ?_
        obtain ⟨c, -, -, hc⟩ := hscalar x x.2
        have h0 : (c : K) = 1 := by
          have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩
            ⟨0, by omega⟩) hc
          simp only [coe_diagHom, Matrix.diagonal_apply_eq, Matrix.GeneralLinearGroup.coe_scalar,
            Matrix.scalar_apply] at this
          rw [← this]
          exact congrArg Units.val hx
        have hc1 : c = 1 := Units.ext h0
        have h1 : E x = 1 := by
          apply diagHom_injective n
          rw [hc, hc1, map_one, map_one]
        exact Subtype.ext (hinj (h1.trans (map_one E).symm))
      have hrange : ev.range ≤ rootsOfUnity p K := by
        rintro _ ⟨x, rfl⟩
        have hx : x ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hpow]; rfl)
        rw [mem_rootsOfUnity, ← map_pow, hx, map_one]
      calc Nat.card θ.ker = Nat.card ev.range :=
            Nat.card_congr (MonoidHom.ofInjective hev).toEquiv
        _ ≤ Nat.card (rootsOfUnity p K) := Subgroup.card_le_of_le hrange
        _ ≤ p := card_rootsOfUnity K p
    ·
      rw [pow_zero]
      have hbot : θ.ker = ⊥ := by
        refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
        obtain ⟨c, hcn, hcp', hc⟩ := hscalar x hx
        have hc1 : c = 1 := by
          have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpn
          have : c ^ Nat.gcd p n = 1 := pow_gcd_eq_one.mpr ⟨hcp', hcn⟩
          rwa [hcop.gcd_eq_one, pow_one] at this
        have h1 : E x = 1 := by
          apply diagHom_injective n
          rw [hc, hc1, map_one, map_one]
        exact hinj (h1.trans (map_one E).symm)
      rw [hbot, Subgroup.card_bot]
  have hDcard : p ^ (m - if p ∣ n then 1 else 0) ≤ Nat.card D := by
    set ε := if p ∣ n then 1 else 0 with hεdef
    by_cases hε : ε ≤ m
    · have h1 : Nat.card θ.ker * Nat.card D = p ^ m := by
        rw [hDdef, ← Subgroup.index_ker, Subgroup.card_mul_index, Nat.card_congr
          Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
          Fintype.card_fin]
      have h2 : p ^ m ≤ Nat.card D * p ^ ε := by
        rw [← h1, mul_comm]
        exact Nat.mul_le_mul_left _ hkercard
      have h3 : p ^ m = p ^ (m - ε) * p ^ ε := by
        rw [← pow_add, Nat.sub_add_cancel hε]
      rw [h3] at h2
      exact Nat.le_of_mul_le_mul_right h2 (pow_pos hp.pos _)
    · rw [Nat.sub_eq_zero_of_le (by omega), pow_zero]
      exact Nat.card_pos
  set z : unitaryPSU hK n := unitaryProj hK n ⟨z₀, hz₀S⟩
  have hz1 : z ≠ 1 := by
    intro h
    have hmem : (⟨z₀, hz₀S⟩ : S) ∈ unitaryScalars hK n := by
      rw [← ker_unitaryProj hK n]
      exact h
    obtain ⟨c, -, -, hc⟩ := mem_unitaryScalars.mp hmem
    exact hz₀sc c hc
  have hz2 : z ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨z₀, hz₀S⟩ : S) ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hz₀2)
    rw [this, map_one]
  have hzD : ∀ x ∈ D, Commute z x := by
    rintro _ ⟨a, rfl⟩
    change Commute (unitaryProj hK n ⟨z₀, hz₀S⟩) (unitaryProj hK n (δ a))
    refine Commute.map ?_ _
    exact Subtype.ext (hz₀c a).eq
  exact exists_involution_elemAbelian_of_cover Y hφ hker hp hp2 hDp hF hDcard hz1 hz2 hzD

end Witness

section Main

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem expHom_injective {p : ℕ} [Fact p.Prime] {J ι M : Type*} [Fintype J] [DecidableEq J]
    [CommGroup M] (c : J → ι → M) (hc : ∀ j i, c j i ^ p = 1)
    (hpriv : ∀ j, ∃ i, (∀ j', j' ≠ j → c j' i = 1) ∧ orderOf (c j i) = p) :
    Function.Injective (expHom c hc) := by
  refine (injective_iff_map_eq_one _).mpr fun a ha => ?_
  apply Multiplicative.toAdd.injective
  funext j
  obtain ⟨i, hi1, hio⟩ := hpriv j
  have h := congrFun ha i
  rw [expHom_apply, Pi.one_apply, Finset.prod_eq_single j
    (fun j' _ hj' => by rw [hi1 j' hj', one_pow]) (fun h => absurd (Finset.mem_univ j) h)] at h
  rw [← orderOf_dvd_iff_pow_eq_one, hio, ← ZMod.natCast_eq_zero_iff, ZMod.natCast_zmod_val] at h
  rw [h]
  rfl

theorem diagHom_expHom_mem_unitarySU (hK : UnitaryFieldData ℓ f K) {p : ℕ} [NeZero p] {n m : ℕ}
    (c : Fin m → Fin n → Kˣ) (hc : ∀ j i, c j i ^ p = 1) (hprod : ∀ j, ∏ i, c j i = 1)
    (hnorm : ∀ j i, c j i ^ (ℓ ^ f + 1) = 1) (a : Multiplicative (Fin m → ZMod p)) :
    diagHom n (expHom c hc a) ∈ unitarySU ℓ f K n := by
  rw [mem_unitarySU_iff hK]
  refine ⟨?_, diagHom_unitary hK fun i => ?_⟩
  · rw [det_diagHom, ← Units.coe_prod]
    simp only [expHom_apply]
    rw [Finset.prod_comm]
    simp_rw [Finset.prod_pow, hprod, one_pow, Finset.prod_const_one, Units.val_one]
  · rw [← Units.val_pow_eq_pow_val, expHom_apply, ← Finset.prod_pow]
    simp_rw [← pow_mul, mul_comm _ (ℓ ^ f + 1), pow_mul, hnorm, one_pow, Finset.prod_const_one,
      Units.val_one]

theorem exists_orderOf_eq_norm_one (hK : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ ℓ ^ f + 1) : ∃ ζ : Kˣ, orderOf ζ = p ∧ ζ ^ (ℓ ^ f + 1) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := hK.finite
  have hcard : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK.card_eq_sq, show (1 : ℕ) = 1 ^ 2 from rfl, Nat.sq_sub_sq]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hcard
  refine ⟨ζ, hζ, ?_⟩
  obtain ⟨k, hk⟩ := hpq
  rw [hk, pow_mul, ← hζ, pow_orderOf_eq_one, one_pow]

theorem unitary_split_prime_central_cover_two_local_rank {G : Type*} [Group G] [Finite G]
    (Y : Subgroup G) (hK : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ ℓ ^ f + 1) {n : ℕ} (hn : 3 ≤ n) (φ : Y →* unitaryPSU hK n)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y) :
    let ε := if p ∣ n then 1 else 0
    let r := if ℓ = 2 then n - 2 - ε else n - 1 - ε
    ∃ u : G, u ∈ Y ∧ orderOf u = 2 ∧ ∃ V : Subgroup G, V ≤ Y ⊓ Subgroup.centralizer {u} ∧
      IsElemAbelian p V ∧ Nat.card V = p ^ r := by
  intro ε r
  classical
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ, hζN⟩ := exists_orderOf_eq_norm_one hK hp hpq
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hn1 : 1 ≤ m + 3 := by omega
  by_cases hℓ2 : ℓ = 2
  ·
    have hchar : CharP K 2 := hℓ2 ▸ hK.charP
    have h2K : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
    have hneg : (-1 : K) = 1 := by linear_combination -h2K
    have hr : r = (m + 1) - ε := by
      simp only [r, hℓ2, ite_true]
      omega
    set c : Fin (m + 1) → Fin (m + 3) → Kˣ := fun j i =>
      if i = 0 ∨ i = 1 then ζ else if i = j.succ.succ then ζ⁻¹ ^ 2 else 1 with hcdef
    have hcp : ∀ j i, c j i ^ p = 1 := by
      intro j i
      simp only [hcdef]
      split_ifs
      · exact hζp
      · rw [← pow_mul, mul_comm, pow_mul, inv_pow, hζp, inv_one, one_pow]
      · exact one_pow p
    have hcnorm : ∀ j i, c j i ^ (ℓ ^ f + 1) = 1 := by
      intro j i
      simp only [hcdef]
      split_ifs
      · exact hζN
      · rw [← pow_mul, mul_comm, pow_mul, inv_pow, hζN, inv_one, one_pow]
      · exact one_pow _
    have hcprod : ∀ j, ∏ i, c j i = 1 := by
      intro j
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      have h0 : c j 0 = ζ := by simp [hcdef]
      have h1 : c j (Fin.succ 0) = ζ := by simp [hcdef, Fin.succ_zero_eq_one]
      have h2 : ∀ i : Fin (m + 1), c j i.succ.succ = if i = j then ζ⁻¹ ^ 2 else 1 := by
        intro i
        simp only [hcdef, Fin.succ_ne_zero, Fin.succ_succ_ne_one, or_self, ite_false,
          Fin.succ_inj]
      simp only [h0, h1, h2, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
      group
    have hpriv : ∀ j, ∃ i, (∀ j', j' ≠ j → c j' i = 1) ∧ orderOf (c j i) = p := by
      intro j
      refine ⟨j.succ.succ, fun j' hj' => ?_, ?_⟩
      · simp only [hcdef, Fin.succ_ne_zero, Fin.succ_succ_ne_one, or_self, ite_false,
          Fin.succ_inj]
        simp [hj'.symm]
      · simp only [hcdef, Fin.succ_ne_zero, Fin.succ_succ_ne_one, or_self, ite_false, ite_true]
        rw [Nat.Coprime.orderOf_pow (by rw [orderOf_inv, hζ]; exact
          (Nat.coprime_primes hp Nat.prime_two).mpr hp2), orderOf_inv, hζ]
    have hswapS : ∀ a b : Fin (m + 3), permGL (Equiv.swap a b) ∈ unitarySU ℓ f K (m + 3) := by
      intro a b
      rw [mem_unitarySU_iff hK]
      refine ⟨?_, permGL_unitary hK _⟩
      rw [det_permGL]
      rcases eq_or_ne a b with rfl | hab
      · rw [Equiv.swap_self, Equiv.Perm.sign_refl]
        simp
      · rw [Equiv.Perm.sign_swap hab]
        simp [hneg]
    have hcswap : ∀ j k : Fin (m + 1), c j ∘ (Equiv.swap j.succ.succ k.succ.succ).symm = c k := by
      intro j k
      funext i
      rw [Function.comp_apply, Equiv.symm_swap]
      have hs0 : Equiv.swap j.succ.succ k.succ.succ 0 = 0 :=
        Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _).symm (Fin.succ_ne_zero _).symm
      have hs1 : Equiv.swap j.succ.succ k.succ.succ 1 = 1 :=
        Equiv.swap_apply_of_ne_of_ne (Fin.succ_succ_ne_one _).symm (Fin.succ_succ_ne_one _).symm
      simp only [hcdef, Equiv.swap_apply_eq_iff, hs0, hs1, Equiv.swap_apply_left]
    have hswap : ∀ j k, j ≠ k → ∃ w ∈ unitarySU ℓ f K (m + 3),
        w * diagHom (m + 3) (c j) * w⁻¹ = diagHom (m + 3) (c k) ∧
          w * diagHom (m + 3) (c k) * w⁻¹ = diagHom (m + 3) (c j) := by
      intro j k _
      refine ⟨permGL (Equiv.swap j.succ.succ k.succ.succ), hswapS _ _, ?_, ?_⟩
      · rw [permGL_mul_diagHom_mul_inv, hcswap]
      · rw [permGL_mul_diagHom_mul_inv, Equiv.swap_comm, hcswap]
    have h01 : (0 : Fin (m + 3)) ≠ 1 := by simp
    have hz₀sc : ∀ c' : Kˣ, permGL (Equiv.swap (0 : Fin (m + 3)) 1) ≠
        Matrix.GeneralLinearGroup.scalar (Fin (m + 3)) c' := fun c' h =>
      permGL_not_mem_statedScalars (fun h' => h01 (Equiv.swap_eq_one_iff.mp h'))
        (show permGL (Equiv.swap (0 : Fin (m + 3)) 1) ∈
          CFSG.Assembly.LowTwoRank.StatedScalars (Fin (m + 3)) K from ⟨c', h.symm⟩)
    have hz₀2 : (permGL (Equiv.swap (0 : Fin (m + 3)) 1) : GL (Fin (m + 3)) K) ^ 2 = 1 := by
      rw [← map_pow, pow_two, Equiv.swap_mul_self, map_one]
    have hc01 : ∀ j i, c j (Equiv.swap (0 : Fin (m + 3)) 1 i) = c j i := by
      intro j i
      have hs : Equiv.swap (0 : Fin (m + 3)) 1 j.succ.succ = j.succ.succ :=
        Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (Fin.succ_succ_ne_one _)
      simp only [hcdef, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left, Equiv.swap_apply_right,
        hs]
      by_cases hi0 : i = 0
      · simp [hi0]
      by_cases hi1 : i = 1
      · simp [hi1]
      simp [hi0, hi1]
    have hz₀c : ∀ a, Commute (permGL (Equiv.swap (0 : Fin (m + 3)) 1))
        (diagHom (m + 3) (expHom (p := p) c hcp a)) := by
      intro a
      have h := permGL_mul_diagHom_mul_inv (K := K) (Equiv.swap (0 : Fin (m + 3)) 1)
        (expHom (p := p) c hcp a)
      have he : expHom (p := p) c hcp a ∘ (Equiv.swap (0 : Fin (m + 3)) 1).symm =
          expHom (p := p) c hcp a := by
        funext i
        simp only [Function.comp_apply, Equiv.symm_swap, expHom_apply, hc01]
      rw [he, mul_inv_eq_iff_eq_mul] at h
      exact h
    obtain ⟨u, huY, hu2, V, hV, hVab, hVcard⟩ := exists_rank_witness Y hK hp hp2 hn1 φ hφ hker
      c hcp (diagHom_expHom_mem_unitarySU hK c hcp hcprod hcnorm) (expHom_injective c hcp hpriv)
      hswap (hswapS 0 1) hz₀sc hz₀2 hz₀c
    exact ⟨u, huY, hu2, V, hV, hVab, by rw [hVcard, hr]⟩
  ·
    have hℓodd : Odd ℓ := hK.prime.odd_of_ne_two hℓ2
    have : CharP K ℓ := hK.charP
    have h2K : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K ℓ]; exact hℓ2)
    have hneg : (-1 : K) ≠ 1 := fun h => h2K (by linear_combination -h)
    have hevenq : Even (ℓ ^ f + 1) := (hℓodd.pow).add_one
    have hr : r = (m + 2) - ε := by
      simp only [r, hℓ2, ite_false]
      omega
    set c : Fin (m + 2) → Fin (m + 3) → Kˣ := fun j i =>
      if i = 0 then ζ else if i = j.succ then ζ⁻¹ else 1 with hcdef
    have hcp : ∀ j i, c j i ^ p = 1 := by
      intro j i
      simp only [hcdef]
      split_ifs
      · exact hζp
      · rw [inv_pow, hζp, inv_one]
      · exact one_pow p
    have hcnorm : ∀ j i, c j i ^ (ℓ ^ f + 1) = 1 := by
      intro j i
      simp only [hcdef]
      split_ifs
      · exact hζN
      · rw [inv_pow, hζN, inv_one]
      · exact one_pow _
    have hcprod : ∀ j, ∏ i, c j i = 1 := by
      intro j
      rw [Fin.prod_univ_succ]
      have h0 : c j 0 = ζ := by simp [hcdef]
      have h1 : ∀ i : Fin (m + 2), c j i.succ = if i = j then ζ⁻¹ else 1 := by
        intro i
        simp only [hcdef, Fin.succ_ne_zero, ite_false, Fin.succ_inj]
      simp only [h0, h1, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
      group
    have hpriv : ∀ j, ∃ i, (∀ j', j' ≠ j → c j' i = 1) ∧ orderOf (c j i) = p := by
      intro j
      refine ⟨j.succ, fun j' hj' => ?_, ?_⟩
      · simp only [hcdef, Fin.succ_ne_zero, ite_false, Fin.succ_inj]
        simp [hj'.symm]
      · simp only [hcdef, Fin.succ_ne_zero, ite_false, ite_true]
        rw [orderOf_inv, hζ]
    have hd₁norm : ∀ (P : Fin (m + 3) → Prop) [DecidablePred P] (i : Fin (m + 3)),
        (((if P i then -1 else 1 : Kˣ)) : K) ^ (ℓ ^ f + 1) = 1 := by
      intro P _ i
      split_ifs
      · rw [Units.val_neg, Units.val_one, hevenq.neg_one_pow]
      · rw [Units.val_one, one_pow]
    have hswap : ∀ j k, j ≠ k → ∃ w ∈ unitarySU ℓ f K (m + 3),
        w * diagHom (m + 3) (c j) * w⁻¹ = diagHom (m + 3) (c k) ∧
          w * diagHom (m + 3) (c k) * w⁻¹ = diagHom (m + 3) (c j) := by
      intro j k hjk
      set σ := Equiv.swap j.succ k.succ with hσ
      set d₁ : Fin (m + 3) → Kˣ := fun i => if i = 0 then -1 else 1 with hd₁
      have hjk' : j.succ ≠ k.succ := fun h => hjk (Fin.succ_injective _ h)
      have hwS : permGL σ * diagHom (m + 3) d₁ ∈ unitarySU ℓ f K (m + 3) := by
        rw [mem_unitarySU_iff hK, Units.val_mul]
        refine ⟨?_, unitary_mul hK (permGL_unitary hK σ)
          (diagHom_unitary hK fun i => hd₁norm (· = 0) i)⟩
        rw [Matrix.det_mul, det_permGL, hσ, Equiv.Perm.sign_swap hjk', det_diagHom,
          Fin.prod_univ_succ]
        simp [hd₁, Fin.succ_ne_zero]
      have hcσ : ∀ a b : Fin (m + 2), c a ∘ (Equiv.swap a.succ b.succ).symm = c b := by
        intro a b
        funext i
        rw [Function.comp_apply, Equiv.symm_swap]
        have hs0 : Equiv.swap a.succ b.succ 0 = 0 :=
          Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _).symm (Fin.succ_ne_zero _).symm
        simp only [hcdef, Equiv.swap_apply_eq_iff, hs0, Equiv.swap_apply_left]
      have hconj : ∀ e : Fin (m + 3) → Kˣ, (permGL σ * diagHom (m + 3) d₁) * diagHom (m + 3) e *
          (permGL σ * diagHom (m + 3) d₁)⁻¹ = diagHom (m + 3) (e ∘ σ.symm) := by
        intro e
        rw [← permGL_mul_diagHom_mul_inv σ e]
        have hcomm := (diagHom_commute (K := K) d₁ e).eq
        calc (permGL σ * diagHom (m + 3) d₁) * diagHom (m + 3) e *
              (permGL σ * diagHom (m + 3) d₁)⁻¹ =
            permGL σ * (diagHom (m + 3) d₁ * diagHom (m + 3) e) * (diagHom (m + 3) d₁)⁻¹ *
              (permGL σ)⁻¹ := by group
          _ = permGL σ * (diagHom (m + 3) e * diagHom (m + 3) d₁) * (diagHom (m + 3) d₁)⁻¹ *
              (permGL σ)⁻¹ := by rw [hcomm]
          _ = permGL σ * diagHom (m + 3) e * (permGL σ)⁻¹ := by group
      refine ⟨_, hwS, ?_, ?_⟩
      · rw [hconj, hσ, hcσ]
      · rw [hconj, hσ, Equiv.swap_comm, hcσ]
    set d₂ : Fin (m + 3) → Kˣ := fun i => if i = 0 ∨ i = 1 then -1 else 1 with hd₂
    have hz₀S : diagHom (m + 3) d₂ ∈ unitarySU ℓ f K (m + 3) := by
      rw [mem_unitarySU_iff hK]
      refine ⟨?_, diagHom_unitary hK fun i => hd₁norm (fun i => i = 0 ∨ i = 1) i⟩
      rw [det_diagHom, Fin.prod_univ_succ, Fin.prod_univ_succ]
      have e0 : ((d₂ 0 : Kˣ) : K) = -1 := by simp [hd₂]
      have e1 : ((d₂ (Fin.succ 0) : Kˣ) : K) = -1 := by simp [hd₂, Fin.succ_zero_eq_one]
      have e2 : ∀ i : Fin (m + 1), ((d₂ i.succ.succ : Kˣ) : K) = 1 := by
        intro i
        simp [hd₂, Fin.succ_ne_zero, Fin.succ_succ_ne_one]
      simp only [e0, e1, e2, Finset.prod_const_one, mul_one]
      ring
    have hz₀sc : ∀ c' : Kˣ, diagHom (m + 3) d₂ ≠
        Matrix.GeneralLinearGroup.scalar (Fin (m + 3)) c' := by
      intro c' h
      have e0 := congrArg
        (fun g : GL (Fin (m + 3)) K => (g : Matrix (Fin (m + 3)) (Fin (m + 3)) K) 0 0) h
      have e2 := congrArg (fun g : GL (Fin (m + 3)) K =>
        (g : Matrix (Fin (m + 3)) (Fin (m + 3)) K) ⟨2, by omega⟩ ⟨2, by omega⟩) h
      simp only [coe_diagHom, Matrix.diagonal_apply_eq, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply] at e0 e2
      have h20 : (⟨2, by omega⟩ : Fin (m + 3)) ≠ 0 := by simp [Fin.ext_iff]
      have h21 : (⟨2, by omega⟩ : Fin (m + 3)) ≠ 1 := by simp [Fin.ext_iff]
      simp only [hd₂, true_or, ite_true, Units.val_neg, Units.val_one, h20, h21, or_self,
        ite_false] at e0 e2
      exact hneg (e0.trans e2.symm)
    have hz₀2 : diagHom (m + 3) d₂ ^ 2 = 1 := by
      rw [← map_pow, ← map_one (diagHom (m + 3))]
      congr 1
      funext i
      simp only [hd₂, Pi.pow_apply, Pi.one_apply]
      split_ifs <;> simp
    obtain ⟨u, huY, hu2, V, hV, hVab, hVcard⟩ := exists_rank_witness Y hK hp hp2 hn1 φ hφ hker
      c hcp (diagHom_expHom_mem_unitarySU hK c hcp hcprod hcnorm) (expHom_injective c hcp hpriv)
      hswap hz₀S hz₀sc hz₀2 (fun a => diagHom_commute _ _)
    exact ⟨u, huY, hu2, V, hV, hVab, by rw [hVcard, hr]⟩

theorem le_localRank_of_unitary_split_prime {G : Type*} [Group G] [Finite G]
    (Y : Subgroup G) (hK : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ ℓ ^ f + 1) {n : ℕ} (hn : 3 ≤ n) (φ : Y →* unitaryPSU hK n)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y) :
    (if ℓ = 2 then n - 2 - (if p ∣ n then 1 else 0) else n - 1 - (if p ∣ n then 1 else 0)) ≤
      localRank p G := by
  obtain ⟨u, -, hu, V, hV, hVab, hVcard⟩ :=
    unitary_split_prime_central_cover_two_local_rank Y hK hp hp3 hpq hn φ hφ hker
  exact le_localRank_of_involution_elemAbelian hp hu (le_inf_iff.mp hV).2 hVab hVcard

end Main

end CFSG.RankThree.Classical2
