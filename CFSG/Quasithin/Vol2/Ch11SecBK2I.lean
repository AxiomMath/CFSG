module

public import CFSG.Quasithin.Vol2.Ch11SecAKA6
public import CFSG.Quasithin.Vol2.Ch11G2Q8OffRealRad
public import CFSG.Quasithin.Vol2.Ch11SecBK2G

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 Matrix
open CFSG.Open (quasithinG2)
open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL)
open scoped IsMulCommutative

namespace BK2

section Nat

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [CommGroup W]
  {H : Subgroup (MulAut W)} {Z : Subgroup W}

omit [Finite K] [CharP K 2] in
theorem exists_linearMap {ι : Type} [Fintype ι] [DecidableEq ι]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {π : ↥Γ →* ↥H} {f : W → (ι → K)}
    (hf : KGNat.IsCoord (KGNat.linModelNat Γ) H Z π f) {a : MulAut W} (haZ : ∀ z ∈ Z, a z ∈ Z)
    (hlin : IsSemiF f (RingHom.id K) a) :
    ∃ T : (ι → K) →ₗ[K] (ι → K), ∀ w, T (f w) = f (a w) := by
  refine ⟨{ toFun := hf.autMap a haZ, map_add' := map_add _, map_smul' := fun c x => ?_ },
    hf.autMap_apply a haZ⟩
  obtain ⟨w, rfl⟩ := hf.surj x
  obtain ⟨w', hw'⟩ := hf.surj (c • f w)
  rw [← hw', hf.autMap_apply, hf.autMap_apply]
  exact hlin c w w' hw'

theorem mem_of_lin_SL3 {π : ↥(StatedSL 3 K) →* ↥H} {f : W → (Fin 3 → K)}
    (hf : KGNat.IsCoord (KGNat.linModelNat (StatedSL 3 K)) H Z π f)
    (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) (hcomm : commV H = ⊤) {a : MulAut W}
    (haH : ∀ h ∈ H, a * h * a⁻¹ ∈ H) (haZ : ∀ z ∈ Z, a z ∈ Z) (ha2 : a * a = 1)
    (hlin : IsSemiF f (RingHom.id K) a) : a ∈ H := by
  obtain ⟨T, hT⟩ := exists_linearMap hf haZ hlin
  have hTT : ∀ x, T (T x) = x := fun x => by
    obtain ⟨w, rfl⟩ := hf.surj x
    rw [hT, hT, ← MulAut.mul_apply, ha2, MulAut.one_apply]
  set A := LinearMap.toMatrix' T with hA
  have hAx : ∀ x, A *ᵥ x = T x := fun x => LinearMap.toMatrix'_mulVec T x
  have hAA : A * A = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      hAx, hAx, hTT]
  have hdet : A.det = 1 := by
    have h1 : A.det ^ 2 ^ 1 = 1 := by rw [pow_one, sq, ← Matrix.det_mul, hAA, Matrix.det_one]
    exact KGNat.eq_one_of_pow_two_pow h1
  have hγ : ∀ w, f (a w) = ((specialLinearGroupEquivStatedSL 3 K ⟨A, hdet⟩ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ f w := fun w => by
    rw [← hT, ← hAx]
    rfl
  rw [eq_pi_of_modZ_nat hf hZ hcomm haH hγ]
  exact (π _).2

omit [Finite K] in
theorem mem_of_lin_Sp4 {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}
    (hf : KGNat.IsCoord (KGNat.linModelNat (StatedSp 2 K)) H Z π f)
    (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) (hcomm : commV H = ⊤) {a : MulAut W}
    (haH : ∀ h ∈ H, a * h * a⁻¹ ∈ H) (haZ : ∀ z ∈ Z, a z ∈ Z) (ha2 : a * a = 1)
    (hlin : IsSemiF f (RingHom.id K) a) : a ∈ H := by
  obtain ⟨T, hT⟩ := exists_linearMap hf haZ hlin
  have hTT : ∀ x, T (T x) = x := fun x => by
    obtain ⟨w, rfl⟩ := hf.surj x
    rw [hT, hT, ← MulAut.mul_apply, ha2, MulAut.one_apply]
  have hnorm : ∀ γ : ↥(StatedSp 2 K), ∃ γ' : ↥(StatedSp 2 K), ∀ v,
      T (((γ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
        ((γ' : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ T v := by
    intro γ
    obtain ⟨γ', hγ'⟩ := hf.onto ⟨_, haH _ (π γ).2⟩
    refine ⟨γ', fun v => ?_⟩
    have hTA : ∀ x, T x = hf.autMap a haZ x := fun x => by
      obtain ⟨w, rfl⟩ := hf.surj x
      rw [hT, hf.autMap_apply]
    have h1 := hf.autMap_lin a haZ γ' γ (congrArg Subtype.val hγ').symm v
    rw [hTA, hTA]
    exact (congrArg (hf.autMap a haZ) (KGNat.linModelNat_lin _ γ v).symm).trans
      (h1.trans (KGNat.linModelNat_lin _ γ' _))
  obtain ⟨c, hc⟩ := KGNat.exists_similitude T hnorm
  have hc1 : c = 1 := KGNat.similitude_eq_one hTT hc
  have hbij : Function.Bijective T :=
    ⟨fun x y h => by rw [← hTT x, ← hTT y, h], fun y => ⟨T y, hTT y⟩⟩
  obtain ⟨N, hN⟩ := KGNat.KA.exists_statedSp_of_isometry hbij fun x y => by
    rw [hc, hc1, one_mul]
  have hγ : ∀ w, f (a w) =
      ((N : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ f w :=
    fun w => by
      rw [← hT]
      exact (hN (f w)).symm
  rw [eq_pi_of_modZ_nat hf hZ hcomm haH hγ]
  exact (π N).2

end Nat

theorem mem_of_lin_G2 {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G]
    {L V X : Subgroup G} [IsMulCommutative ↥V]
    {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥(autOn L V)} {f : ↥V → (Ix3 → K)}
    (hf : KGNat.IsCoord (G2Q8.lmG K) (autOn L V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
    {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1) {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (hcomm : commV (autOn L V) = ⊤)
    (hXN : X ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G))
    {a : MulAut ↥V} (haX : a ∈ autOn X V) (ha2 : a * a = 1)
    (haZ : ∀ z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V,
      a z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V)
    (hlin : IsSemiF f (RingHom.id K) a) : a ∈ autOn L V := by
  obtain ⟨x, hxX, hxV, rfl⟩ := SecA.mem_autOn_iff.mp haX
  obtain ⟨c, γ, σ, hc, hcγ⟩ := G2Q8.exists_smul_frob_conjV hf hc0 hc1 hK hn hXN ⟨hxX, hxV⟩
  have hx₀ : (q6 (1 : K) 0 0 0 0 0) ≠ 0 := fun h => one_ne_zero (congrFun h (.inl 0))
  obtain ⟨w, hw⟩ := hf.surj (q6 1 0 0 0 0 0)
  have hne : f (SecA.conjV V x hxV w) ≠ 0 := by
    intro h0
    have h2 := haZ _ ((hf.ker _).mp h0)
    rw [← MulAut.mul_apply, ha2, MulAut.one_apply] at h2
    exact hx₀ (hw ▸ (hf.ker w).mpr h2)
  have hσ : ∀ d, σ d = d := by
    intro d
    obtain ⟨w', hw'⟩ := hf.surj (d • f w)
    have h1 := hlin d w w' hw'
    rw [hcγ, hcγ, hw', G2Q8.frobQ_smul, G2Q8.g2Act_smul, smul_comm c, RingHom.id_apply,
      ← hcγ] at h1
    exact smul_left_injective K hne h1
  have hfrob : ∀ y, G2Q8.frobQ (σ : K →+* K) y = y := fun y => funext fun j => hσ (y j)
  have hγ : ∀ v, f (SecA.conjV V x hxV v) = c • g2Act γ (f v) := fun v => by rw [hcγ, hfrob]
  rw [G2Q8.eq_rhoG_of_smul hf hc0 hc1 hcomm hXN haX ha2 hc hγ]
  exact (G2Q8.rhoG hc0 hc1 π γ).2

end BK2

end CFSG.Quasithin.Vol2.Ch11.SecB
