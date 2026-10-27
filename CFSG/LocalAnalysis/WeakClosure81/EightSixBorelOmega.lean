module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveBars

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G] {V H T : Subgroup G}

private theorem borel86_omega_pow_comm_mem_pCoreOf {K O : Subgroup G}
    (hKO : K ≤ Subgroup.normalizer (O : Set G)) {y : G} (hyK : y ∈ K)
    (hcomm : ∀ x ∈ K, y * x * y⁻¹ * x⁻¹ ∈ O) (j : ℕ) :
    ∀ x ∈ K, y ^ j * x * (y ^ j)⁻¹ * x⁻¹ ∈ O := by
  induction j with
  | zero =>
    intro x _
    simpa using O.one_mem
  | succ j ih =>
    intro x hx
    have hconj : y ^ j * (y * x * y⁻¹ * x⁻¹) * (y ^ j)⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (hKO (K.pow_mem hyK j))
        (y * x * y⁻¹ * x⁻¹)).mp (hcomm x hx)
    have he : y ^ (j + 1) * x * (y ^ (j + 1))⁻¹ * x⁻¹ =
        (y ^ j * (y * x * y⁻¹ * x⁻¹) * (y ^ j)⁻¹) *
          (y ^ j * x * (y ^ j)⁻¹ * x⁻¹) := by
      rw [pow_succ]
      group
    rw [he]
    exact O.mul_mem hconj (ih x hx)

private theorem borel86_omega_mem_conjSubgroup_subgroupOf_iff {A H : Subgroup G} {x g : G}
    (hx : x ∈ H) (hg : g ∈ H) :
    (⟨x, hx⟩ : ↥H) ∈ conjSubgroup (A.subgroupOf H) ⟨g, hg⟩ ↔ x ∈ conjSubgroup A g := by
  rw [mem_conjSubgroup_iff, mem_conjSubgroup_iff, Subgroup.mem_subgroupOf]
  constructor <;> intro h <;> simpa using h

theorem mem_eCentSet_of_mem_centerPre (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T) {y : G}
    (hy : y ∈ centerPre (kGenIn V H) (eCentSet V H T)) (hyy : y * y ∈ eCentSet V H T) :
    y ∈ eCentSet V H T := by
  obtain ⟨hyK, hyc⟩ := hy
  obtain ⟨r, b, hbodd, horder⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have hcomm : ∀ x ∈ kGenIn V H, y * x * y⁻¹ * x⁻¹ ∈ pCoreOf 2 (kGenIn V H) :=
    h.comm_mem_pCoreOf_of_mem_centerPre hKT ⟨hyK, hyc⟩
  have hpow : ∀ x ∈ kGenIn V H,
      y ^ b * x * (y ^ b)⁻¹ * x⁻¹ ∈ pCoreOf 2 (kGenIn V H) :=
    borel86_omega_pow_comm_mem_pCoreOf
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (kGenIn V H)) hyK hcomm b
  have hbO : y ^ b ∈ pCoreOf 2 (kGenIn V H) := by
    refine mem_pCoreOf_of_comm_mem_of_pow_mem (K := kGenIn V H) (c := y ^ b)
      ((kGenIn V H).pow_mem hyK b) hpow (n := r) ?_
    have h1 : (y ^ b) ^ 2 ^ r = 1 := by
      rw [← pow_mul, Nat.mul_comm, ← horder, pow_orderOf_eq_one]
    rw [h1]
    exact (pCoreOf 2 (kGenIn V H)).one_mem
  have hbC : y ^ b ∈ Subgroup.centralizer (eSub V H T : Set G) :=
    h.pCoreOf_kGenIn_le_centralizer_eSub hbO
  obtain ⟨j, hj⟩ := hbodd
  have hy_eq : y = y ^ b * ((y * y) ^ j)⁻¹ := by
    rw [hj, pow_succ', pow_mul, ← pow_two y, mul_inv_cancel_right]
  show y ∈ Subgroup.centralizer (eSub V H T : Set G)
  rw [hy_eq]
  exact (Subgroup.centralizer (eSub V H T : Set G)).mul_mem hbC
    ((Subgroup.centralizer (eSub V H T : Set G)).inv_mem
      ((Subgroup.centralizer (eSub V H T : Set G)).pow_mem hyy j))

theorem conjSubgroup_eq_of_inv_mul_mem_eCentSet (h : Hyp83 V H T) (hKT : H = kGenIn V H ⊔ T)
    {a a' x x' : G} (ha : a ∈ H) (ha' : a' ∈ H)
    (hx : x ∈ conjSubgroup V a) (hxE : x ∉ eCentSet V H T) (hx' : x' ∈ conjSubgroup V a')
    (hxx' : x⁻¹ * x' ∈ eCentSet V H T) : conjSubgroup V a = conjSubgroup V a' := by
  have hxK : x ∈ kGenIn V H := by
    have hxV : a * x * a⁻¹ ∈ V := mem_conjSubgroup_iff.mp hx
    have hmem : a⁻¹ * (a * x * a⁻¹) * (a⁻¹)⁻¹ ∈ conjClosure V H :=
      mem_conjClosure (H.inv_mem ha) hxV
    have he : a⁻¹ * (a * x * a⁻¹) * (a⁻¹)⁻¹ = x := by group
    rw [he] at hmem
    rwa [h.conjClosure_eq_kGenIn hKT] at hmem
  have hx'K : x' ∈ kGenIn V H := by
    have hx'V : a' * x' * a'⁻¹ ∈ V := mem_conjSubgroup_iff.mp hx'
    have hmem : a'⁻¹ * (a' * x' * a'⁻¹) * (a'⁻¹)⁻¹ ∈ conjClosure V H :=
      mem_conjClosure (H.inv_mem ha') hx'V
    have he : a'⁻¹ * (a' * x' * a'⁻¹) * (a'⁻¹)⁻¹ = x' := by group
    rw [he] at hmem
    rwa [h.conjClosure_eq_kGenIn hKT] at hmem
  have hx2 : x * x = 1 := by
    have := (isElemAbelian_conjSubgroup' h.elemAbelian a).2 x hx
    simpa [pow_two] using this
  have hx'2 : x' * x' = 1 := by
    have := (isElemAbelian_conjSubgroup' h.elemAbelian a').2 x' hx'
    simpa [pow_two] using this
  let c : G := x⁻¹ * x'
  have hcK : c ∈ kGenIn V H := by
    show x⁻¹ * x' ∈ kGenIn V H
    exact (kGenIn V H).mul_mem ((kGenIn V H).inv_mem hxK) hx'K
  have hcC : c ∈ Subgroup.centralizer (eSub V H T : Set G) :=
    show x⁻¹ * x' ∈ Subgroup.centralizer (eSub V H T : Set G) from hxx'
  have hcc : c * c = c * x * c⁻¹ * x⁻¹ := by
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    have hxe : x' = x * c := by
      show x' = x * (x⁻¹ * x')
      rw [mul_inv_cancel_left]
    have hxc : x * c * x = c⁻¹ := by
      have h1 : (x * c * x)⁻¹ = c := by
        apply inv_eq_of_mul_eq_one_right
        rw [hxe] at hx'2
        simpa [mul_assoc] using hx'2
      calc x * c * x = ((x * c * x)⁻¹)⁻¹ := (inv_inv (x * c * x)).symm
        _ = c⁻¹ := by rw [h1]
    have hcx : x * c⁻¹ * x = c := by
      have h1 : (x * c * x)⁻¹ = c := by rw [hxc, inv_inv]
      have h2 : (x * c * x)⁻¹ = x * c⁻¹ * x := by
        rw [mul_inv_rev, mul_inv_rev, hxinv]
        group
      rwa [h2] at h1
    calc c * c = c * (x * c⁻¹ * x) := by rw [hcx]
      _ = c * (x * c⁻¹ * x⁻¹) := by rw [hxinv]
      _ = c * x * c⁻¹ * x⁻¹ := by group
  have hccO : c * c ∈ pCoreOf 2 (kGenIn V H) := by
    rw [hcc]
    exact h.comm_mem_pCoreOf_of_mem_inf_centralizer hKT hcC x hxK
  have hcO : c ∈ pCoreOf 2 (kGenIn V H) :=
    h.mem_pCoreOf_of_mem_inf_centralizer_of_pow hKT hcK hcC (n := 1)
      (by simpa [pow_two] using hccO)
  let v : G := a * x * a⁻¹
  let v' : G := a * x' * a⁻¹
  have hvV : v ∈ V := by
    show a * x * a⁻¹ ∈ V
    exact mem_conjSubgroup_iff.mp hx
  have hv'conj : v' ∈ conjSubgroup V (a' * a⁻¹) := by
    rw [mem_conjSubgroup_iff]
    have he : (a' * a⁻¹) * (a * x' * a⁻¹) * (a' * a⁻¹)⁻¹ = a' * x' * a'⁻¹ := by group
    rw [he]
    exact mem_conjSubgroup_iff.mp hx'
  have hxv : a⁻¹ * v * (a⁻¹)⁻¹ = x := by
    show a⁻¹ * (a * x * a⁻¹) * (a⁻¹)⁻¹ = x
    group
  have hvO : v ∉ pCoreOf 2 (kGenIn V H) := by
    intro hvO'
    apply hxE
    have hvC : v ∈ Subgroup.centralizer (eSub V H T : Set G) :=
      h.pCoreOf_kGenIn_le_centralizer_eSub hvO'
    have h1 := h.conj_mem_centralizer_eSub (H.inv_mem ha) hvC
    show x ∈ Subgroup.centralizer (eSub V H T : Set G)
    rwa [hxv] at h1
  have hON : H ≤ Subgroup.normalizer (pCoreOf 2 (kGenIn V H) : Set G) :=
    (h.le_normalizer_kGenIn_of_eq_sup hKT).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (kGenIn V H))
  have hacO : a * c * a⁻¹ ∈ pCoreOf 2 (kGenIn V H) :=
    (Subgroup.mem_normalizer_iff.mp (hON ha) c).mp hcO
  have hvv' : v⁻¹ * v' = a * c * a⁻¹ := by
    show (a * x * a⁻¹)⁻¹ * (a * x' * a⁻¹) = a * (x⁻¹ * x') * a⁻¹
    group
  have hvH : v ∈ H := h.le_H hvV
  have hx'H : x' ∈ H := kGenIn_le_H h.le_H hx'K
  have hv'H : v' ∈ H := H.mul_mem (H.mul_mem ha hx'H) (H.inv_mem ha)
  let Vh : Subgroup ↥H := V.subgroupOf H
  let Eh : Subgroup ↥H := eSub Vh ⊤ (T.subgroupOf H)
  let Jh : Subgroup ↥H := pCoreOf 2 (kSub Vh ⊤ Eh)
  have h73 : SevenK.Hyp73 Vh ⊤ Eh Jh := (AmbientH.hyp711 h hKT).toHyp73
  have hJeq : Jh = (pCoreOf 2 (kGenIn V H)).subgroupOf H := by
    dsimp only [Jh, Vh, Eh]
    rw [AmbientH.kSub_eq_kGenIn h hKT]
    exact pCoreOf_subgroupOf (kGenIn_le_H h.le_H)
  have hha : (⟨v, hvH⟩ : ↥H) ∈ Vh := Subgroup.mem_subgroupOf.mpr hvV
  have hhaJ : (⟨v, hvH⟩ : ↥H) ∉ Jh := by
    intro hvJ
    exact hvO (by rw [hJeq] at hvJ; exact Subgroup.mem_subgroupOf.mp hvJ)
  have hha' : (⟨v', hv'H⟩ : ↥H) ∈
      conjSubgroup Vh ⟨a' * a⁻¹, H.mul_mem ha' (H.inv_mem ha)⟩ :=
    (borel86_omega_mem_conjSubgroup_subgroupOf_iff hv'H
      (H.mul_mem ha' (H.inv_mem ha))).mpr hv'conj
  have hhaJ' : (⟨v, hvH⟩ : ↥H)⁻¹ * ⟨v', hv'H⟩ ∈ Jh := by
    rw [hJeq]
    apply Subgroup.mem_subgroupOf.mpr
    show v⁻¹ * v' ∈ pCoreOf 2 (kGenIn V H)
    rw [hvv']
    exact hacO
  obtain ⟨j, hjJ, hjEq⟩ :=
    seven_three_four_ti (G := ↥H) (V := Vh) (H := ⊤) (E := Eh) (J := Jh)
      h73.elemAbelian h73.ti h73.abelian h73.le h73.normal h73.mem h73.omega_le
      h73.pcore_le h73.jnormal h73.iSub_le
      (h := (⟨a' * a⁻¹, H.mul_mem ha' (H.inv_mem ha)⟩ : ↥H)) trivial
      hha hhaJ hha' hhaJ'
  have hjO : (j : G) ∈ pCoreOf 2 (kGenIn V H) := by
    rw [hJeq] at hjJ
    exact Subgroup.mem_subgroupOf.mp hjJ
  have hjN : (j : G) ∈ Subgroup.normalizer (V : Set G) := by
    have h1 := h.mem_normalizer_conjSubgroup_of_mem_centralizer (k := 1) H.one_mem
      (h.pCoreOf_kGenIn_le_centralizer_eSub hjO)
    rwa [conjSubgroup_one] at h1
  have hconjG : conjSubgroup V (a' * a⁻¹) = V := by
    have hmap : conjSubgroup V (a' * a⁻¹) = conjSubgroup V (j : G) := by
      have h1 := congrArg (Subgroup.map H.subtype) hjEq
      rwa [map_conjSubgroup_subgroupOf h.le_H (H.mul_mem ha' (H.inv_mem ha)),
        map_conjSubgroup_subgroupOf h.le_H j.2] at h1
    rw [hmap]
    exact conjSubgroup_eq_iff_mem_normalizer.mpr hjN
  exact (show conjSubgroup V a' = conjSubgroup V a from by
    calc conjSubgroup V a' = conjSubgroup V ((a' * a⁻¹) * a) := by
          rw [inv_mul_cancel_right]
      _ = conjSubgroup (conjSubgroup V (a' * a⁻¹)) a :=
          (conjSubgroup_conjSubgroup V (a' * a⁻¹) a).symm
      _ = conjSubgroup V a := by rw [hconjG]).symm

end CFSG.LocalAnalysis.WeakClosure81

end
