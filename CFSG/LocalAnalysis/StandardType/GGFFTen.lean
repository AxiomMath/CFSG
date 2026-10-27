module

public import CFSG.LocalAnalysis.StandardType.GGFFLocal
public import CFSG.RankThree.PartTwo.Sec21.FF81P51
public import CFSG.RankThree.PartTwo.Sec21.FF81P51Ten
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.GGFF.Setting

open SettingCore

open CFSG.RankThree.PartTwo.Sec21.FF79 (Cen CenS Nor)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

variable {G : Type} [Group G] {b : G} {K : Subgroup G} {z : Fin 3 → K}

private theorem comm_of_mem_D (h : Setting b K z) {d y : G} (hdK : d ∈ CenS K)
    (hdb : d ∈ Cen b) (hy : y ∈ Bt b z) : d * y = y * d := by
  obtain ⟨j, v, rfl⟩ := h.mem_Bt.mp hy
  have hb : d * b ^ j = b ^ j * d :=
    (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hdb) j).eq
  have hv : d * vecElt (zs z) v = vecElt (zs z) v * d :=
    (Subgroup.mem_centralizer_iff.mp hdK _ (tor_le z (vecElt_mem_tor _ v))).symm
  calc d * (b ^ j * vecElt (zs z) v) = (d * b ^ j) * vecElt (zs z) v := by group
    _ = (b ^ j * d) * vecElt (zs z) v := by rw [hb]
    _ = b ^ j * (d * vecElt (zs z) v) := by group
    _ = b ^ j * (vecElt (zs z) v * d) := by rw [hv]
    _ = (b ^ j * vecElt (zs z) v) * d := by group

private theorem comm_of_conj_comm {n t x : G}
    (h : t * (n * x * n⁻¹) = (n * x * n⁻¹) * t) :
    (n⁻¹ * t * n) * x = x * (n⁻¹ * t * n) := by
  calc (n⁻¹ * t * n) * x = n⁻¹ * (t * (n * x * n⁻¹)) * n := by group
    _ = n⁻¹ * ((n * x * n⁻¹) * t) * n := by rw [h]
    _ = x * (n⁻¹ * t * n) := by group

private theorem eq_one_of_pow_five_pow (hno : ∀ x : K, x ^ 5 = 1 → x * z 0 = z 0 * x →
    x * z 1 = z 1 * x → x = 1) (j : ℕ) (x : K) (hx : x ^ (5 ^ j) = 1)
    (h0 : x * z 0 = z 0 * x) (h1 : x * z 1 = z 1 * x) : x = 1 := by
  induction j generalizing x with
  | zero => simpa using hx
  | succ j ih =>
    have hx5 : (x ^ 5) ^ (5 ^ j) = 1 := by
      rw [← pow_mul, ← pow_succ']
      exact hx
    have h0' : x ^ 5 * z 0 = z 0 * x ^ 5 :=
      (Commute.pow_left (show Commute x (z 0) from h0) 5).eq
    have h1' : x ^ 5 * z 1 = z 1 * x ^ 5 :=
      (Commute.pow_left (show Commute x (z 1) from h1) 5).eq
    exact hno x (ih (x ^ 5) hx5 h0' h1') h0 h1

variable [Finite G]

private theorem conjAut_pow_apply (h : Setting b K z) {r : G} (hr : r ∈ Cen b) (m : ℕ) (y : K) :
    ((((conjAut (h.nor r hr)) ^ m) y : K) : G) = r ^ m * (y : G) * (r ^ m)⁻¹ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', MulAut.mul_apply]
    calc (((conjAut (h.nor r hr)) (((conjAut (h.nor r hr)) ^ m) y) : K) : G)
        = r * ((((conjAut (h.nor r hr)) ^ m) y : K) : G) * r⁻¹ := by rw [conjAut_apply]
      _ = r * (r ^ m * (y : G) * (r ^ m)⁻¹) * r⁻¹ := by rw [ih]
      _ = r ^ (m + 1) * (y : G) * (r ^ (m + 1))⁻¹ := by
            rw [pow_succ]
            group

theorem not_five_conj (h : Setting b K z) {f n : G} (hfK : f ∈ K) (hf1 : f ≠ 1) (hf5 : f ^ 5 = 1)
    (hE : ∀ x ∈ ({b, zs z 0, zs z 1} : Set G),
      n * x * n⁻¹ ∈ Bt b z ∧ f * (n * x * n⁻¹) = n * x * n⁻¹ * f) : False := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let D : Subgroup G := CenS K ⊓ Cen b
  have hDmem : ∀ {x : G}, x ∈ D ↔ x ∈ CenS K ∧ x ∈ Cen b := by
    intro x
    dsimp only [D]
    exact Subgroup.mem_inf
  obtain ⟨S⟩ := Sylow.nonempty (p := 5) (G := D)
  let S' : Subgroup G := (S : Subgroup D).map D.subtype
  let T : Subgroup G := Subgroup.zpowers f ⊔ S'
  have hS'le : S' ≤ D := Subgroup.map_subtype_le (S : Subgroup D)
  have hf_notS' : f ∉ S' := by
    intro hfS'
    have hfD := hS'le hfS'
    exact hf1 (h.eq_one_of_mem hfK fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (hDmem.mp hfD).1 y hy).symm)
  have hford : orderOf f = 5 := by
    have hdvd : orderOf f ∣ 5 := orderOf_dvd_iff_pow_eq_one.mpr hf5
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h5
    · exact absurd (orderOf_eq_one_iff.mp h1) hf1
    · exact h5
  have hfp : IsPGroup 5 (Subgroup.zpowers f) :=
    IsPGroup.of_card (G := Subgroup.zpowers f) (n := 1)
      (by rw [Nat.card_zpowers, hford, pow_one])
  have hS'p : IsPGroup 5 S' := S.isPGroup'.map D.subtype
  have hS'norm : S' ≤ Subgroup.normalizer (Subgroup.zpowers f : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro s hs k hk
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    have hsD := hDmem.mp (hS'le hs)
    have hsf : s * f * s⁻¹ = f := by
      have hc : f * s = s * f := (Subgroup.mem_centralizer_iff.mp hsD.1) f hfK
      rw [← hc]
      group
    have h2 : (MulAut.conj s) (f ^ j) = f ^ j := by
      rw [map_zpow, MulAut.conj_apply, hsf]
    have hmem : (MulAut.conj s) (f ^ j) ∈ Subgroup.zpowers f := by
      rw [h2]
      exact Subgroup.zpow_mem_zpowers f j
    simpa only [MulAut.conj_apply] using hmem
  have hTp : IsPGroup 5 T := by
    dsimp only [T]
    exact IsPGroup.to_sup_of_normal_left' hfp hS'p hS'norm
  have hcent : ∀ (x : G) (hx : x ∈ ({b, zs z 0, zs z 1} : Set G)) (t : G), t ∈ T →
      t * (n * x * n⁻¹) = (n * x * n⁻¹) * t := by
    intro x hx t ht
    have hEx := hE x hx
    have hTle : T ≤ Subgroup.centralizer ({n * x * n⁻¹} : Set G) := by
      dsimp only [T]
      refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hEx.2))
        ?_
      intro s hs
      have hsD := hDmem.mp (hS'le hs)
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (comm_of_mem_D h hsD.1 hsD.2 hEx.1)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hTle ht)
  have hS'ltT : S' < T := by
    refine lt_of_le_of_ne le_sup_right ?_
    intro heq
    have hfT : f ∈ T := Subgroup.mem_sup_left (Subgroup.mem_zpowers f)
    exact hf_notS' (le_of_eq heq.symm hfT)
  have hcard_lt : Nat.card S' < Nat.card T := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hS'ltT.le) ?_
    intro hcard
    exact hS'ltT.ne (Subgroup.eq_of_le_of_card_ge hS'ltT.le (le_of_eq hcard.symm))
  let R : Subgroup G := T.map (MulAut.conj n⁻¹).toMonoidHom
  have hRT : Nat.card R = Nat.card T := by
    dsimp only [R]
    exact Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective
  have hRp : IsPGroup 5 R := by
    dsimp only [R]
    exact hTp.map (MulAut.conj n⁻¹).toMonoidHom
  have hRle : R ≤ D := by
    intro r hr
    obtain ⟨t, htT, htr⟩ := Subgroup.mem_map.mp hr
    have hr_eq : r = n⁻¹ * t * n := by
      rw [← htr]
      simp
    have hrb : r * b = b * r := by
      rw [hr_eq]
      exact comm_of_conj_comm (hcent b (by simp) t htT)
    have hrz0 : r * zs z 0 = zs z 0 * r := by
      rw [hr_eq]
      exact comm_of_conj_comm (hcent (zs z 0) (by simp) t htT)
    have hrz1 : r * zs z 1 = zs z 1 * r := by
      rw [hr_eq]
      exact comm_of_conj_comm (hcent (zs z 1) (by simp) t htT)
    have hrCen : r ∈ Cen b := Subgroup.mem_centralizer_singleton_iff.mpr hrb
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf (p := 5) (G := R)).mp hRp ⟨r, hr⟩
    have hrpow : r ^ (5 ^ j) = 1 := by
      have hpow := pow_orderOf_eq_one (⟨r, hr⟩ : R)
      rw [hj] at hpow
      simpa using congrArg Subtype.val hpow
    have hodd : Odd (5 ^ j) := Odd.pow (n := j) (by norm_num : Odd 5)
    have hpoweq : (conjAut (h.nor r hrCen)) ^ (5 ^ j) = 1 := by
      ext y
      rw [conjAut_pow_apply h hrCen, hrpow]
      simp
    obtain ⟨κ, hκ⟩ := h.model.inner_odd (conjAut (h.nor r hrCen)) (5 ^ j) hodd hpoweq
    have hαz0 : conjAut (h.nor r hrCen) (z 0) = z 0 := by
      apply Subtype.ext
      rw [conjAut_apply]
      have h1 : r * zs z 0 * r⁻¹ = zs z 0 := by
        rw [hrz0]
        group
      simpa using h1
    have hαz1 : conjAut (h.nor r hrCen) (z 1) = z 1 := by
      apply Subtype.ext
      rw [conjAut_apply]
      have h1 : r * zs z 1 * r⁻¹ = zs z 1 := by
        rw [hrz1]
        group
      simpa using h1
    have hκz0 : κ * z 0 = z 0 * κ := by
      have h1 : (MulAut.conj κ) (z 0) = z 0 := hκ ▸ hαz0
      rw [MulAut.conj_apply] at h1
      calc κ * z 0 = (κ * z 0 * κ⁻¹) * κ := by group
        _ = z 0 * κ := by rw [h1]
    have hκz1 : κ * z 1 = z 1 * κ := by
      have h1 : (MulAut.conj κ) (z 1) = z 1 := hκ ▸ hαz1
      rw [MulAut.conj_apply] at h1
      calc κ * z 1 = (κ * z 1 * κ⁻¹) * κ := by group
        _ = z 1 * κ := by rw [h1]
    have hκpow : κ ^ (5 ^ j) = 1 := by
      apply h.model.eq_one_of_forall_comm
      intro y
      have hconj : MulAut.conj (κ ^ (5 ^ j)) = 1 := by
        rw [map_pow, ← hκ]
        exact hpoweq
      have hy : (MulAut.conj (κ ^ (5 ^ j))) y = y := by simp [hconj]
      rw [MulAut.conj_apply] at hy
      calc κ ^ (5 ^ j) * y = (κ ^ (5 ^ j) * y * (κ ^ (5 ^ j))⁻¹) * κ ^ (5 ^ j) := by
            group
        _ = y * κ ^ (5 ^ j) := by rw [hy]
    have hκ1 : κ = 1 := eq_one_of_pow_five_pow h.model.no_five j κ hκpow hκz0 hκz1
    have hα1 : conjAut (h.nor r hrCen) = 1 := by
      rw [hκ, hκ1]
      simp
    have hrK : r ∈ CenS K := by
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      have h1 : ((conjAut (h.nor r hrCen)) ⟨y, hy⟩ : K) = ⟨y, hy⟩ := by
        rw [hα1]
        rfl
      have h2 : r * y * r⁻¹ = y := by
        simpa only [conjAut_apply] using congrArg Subtype.val h1
      have h3 : r * y = y * r := by
        simpa using congrArg (· * r) h2
      exact h3.symm
    exact hDmem.mpr ⟨hrK, hrCen⟩
  have hRDp : IsPGroup 5 (R.subgroupOf D) :=
    IsPGroup.of_equiv hRp (Subgroup.subgroupOfEquivOfLe hRle).symm
  have hcard_sub : Nat.card (R.subgroupOf D) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRle).toEquiv
  have hcle : Nat.card (R.subgroupOf D) ≤ 5 ^ (Nat.card D).factorization 5 :=
    CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.card_le_of_isPGroup (p := 5) (G := D)
      (H := R.subgroupOf D) hRDp
  have hSyl : Nat.card (S : Subgroup D) = 5 ^ (Nat.card D).factorization 5 :=
    S.card_eq_multiplicity
  have hcardS' : Nat.card S' = Nat.card (S : Subgroup D) := by
    dsimp only [S']
    exact Subgroup.card_map_of_injective D.subtype_injective
  omega

section Five

open CFSG.RankThree.PartTwo.Sec21.FF81.P51 (V GL4 Mat e psi0 FiveInv)
open CFSG.RankThree.PartTwo.Sec21.FF81.P51T
open Matrix
open scoped IsMulCommutative

private theorem eq_of_psi0 : ∀ v : V, psi0 ⬝ᵥ v = 0 →
    (v 0).val • e 0 + (v 1).val • e 1 + (v 2).val • (e 2 + e 3) = v := by
  decide +kernel

private theorem cvG_pow {B : Subgroup G} [CFSG.IsElementaryAbelian 3 B]
    (β : Module.Basis (Fin 4) (ZMod 3) (Additive B)) {g : G} (hg : g ∈ B) (k : ℕ) :
    cvG β (g ^ k) = k • cvG β g := by
  induction k with
  | zero => rw [pow_zero, zero_smul, cvG_one]
  | succ k ih => rw [pow_succ, cvG_mul β (B.pow_mem hg k) hg, ih, succ_nsmul]

theorem comm_of_psi0 [CFSG.IsElementaryAbelian 3 (Bt b z)]
    (β : Module.Basis (Fin 4) (ZMod 3) (Additive (Bt b z)))
    (hβ : ∀ i, ((Additive.toMul (β i) : Bt b z) : G) = ![b, zs z 0, zs z 1, zs z 2] i)
    {f y : G} (hfb : f * b = b * f) (hf0 : f * zs z 0 = zs z 0 * f)
    (hf12 : f * (zs z 1 * zs z 2) = zs z 1 * zs z 2 * f) (hy : y ∈ Bt b z)
    (hpsi : psi0 ⬝ᵥ cvG β y = 0) : f * y = y * f := by
  have hcv : ∀ i, cvG β (((Additive.toMul (β i) : Bt b z) : G)) = e i := fun i => by
    rw [cvG_of_mem β (Additive.toMul (β i)).2]
    exact cv_basis β i
  have hb0 : cvG β b = e 0 := by
    have h1 := hcv 0
    rw [hβ] at h1
    exact h1
  have hz0 : cvG β (zs z 0) = e 1 := by
    have h1 := hcv 1
    rw [hβ] at h1
    exact h1
  have hz12 : cvG β (zs z 1 * zs z 2) = e 2 + e 3 := by
    have h1 := hcv 2
    have h2 := hcv 3
    rw [hβ] at h1 h2
    rw [cvG_mul β (zs_mem_Bt b z 1) (zs_mem_Bt b z 2)]
    exact congrArg₂ (· + ·) h1 h2
  have hbB := b_mem_Bt b z
  have hz0B := zs_mem_Bt b z 0
  have hz12B := (Bt b z).mul_mem (zs_mem_Bt b z 1) (zs_mem_Bt b z 2)
  set v := cvG β y with hv
  have hy' : b ^ (v 0).val * zs z 0 ^ (v 1).val * (zs z 1 * zs z 2) ^ (v 2).val ∈ Bt b z :=
    (Bt b z).mul_mem ((Bt b z).mul_mem ((Bt b z).pow_mem hbB _) ((Bt b z).pow_mem hz0B _))
      ((Bt b z).pow_mem hz12B _)
  have hyy : y = b ^ (v 0).val * zs z 0 ^ (v 1).val * (zs z 1 * zs z 2) ^ (v 2).val := by
    refine cvG_inj β hy hy' ?_
    rw [cvG_mul β ((Bt b z).mul_mem ((Bt b z).pow_mem hbB _) ((Bt b z).pow_mem hz0B _))
        ((Bt b z).pow_mem hz12B _), cvG_mul β ((Bt b z).pow_mem hbB _) ((Bt b z).pow_mem hz0B _),
      cvG_pow β hbB, cvG_pow β hz0B, cvG_pow β hz12B, hb0, hz0, hz12]
    exact (eq_of_psi0 v hpsi).symm
  rw [hyy]
  have c1 : Commute f b := hfb
  have c2 : Commute f (zs z 0) := hf0
  have c3 : Commute f (zs z 1 * zs z 2) := hf12
  exact (((c1.pow_right _).mul_right (c2.pow_right _)).mul_right (c3.pow_right _)).eq

theorem fiveInv (h : Setting b K z) [CFSG.IsElementaryAbelian 3 (Bt b z)]
    (β : Module.Basis (Fin 4) (ZMod 3) (Additive (Bt b z)))
    (hβ : ∀ i, ((Additive.toMul (β i) : Bt b z) : G) = ![b, zs z 0, zs z 1, zs z 2] i) :
    FiveInv (ρU β).range := by
  rintro g ⟨⟨n, hn⟩, rfl⟩ ⟨h0, h1, h2⟩
  have hcol : ∀ i, psi0 ⬝ᵥ (((ρU β ⟨n, hn⟩ : GL4) : Mat) *ᵥ e i) =
      psi0 ⬝ᵥ cvG β (n * ![b, zs z 0, zs z 1, zs z 2] i * n⁻¹) := fun i => by
    rw [coe_ρU, ρM_col, hβ]
  obtain ⟨f, hf1, hf5, hf0, hf12⟩ := h.model.five
  have hfb : (f : G) * b = b * f := h.comm_of_mem f.2
  have hf0' : (f : G) * zs z 0 = zs z 0 * f := by
    simpa only [Subgroup.coe_mul] using congrArg Subtype.val hf0
  have hf12' : (f : G) * (zs z 1 * zs z 2) = zs z 1 * zs z 2 * f := by
    simpa only [Subgroup.coe_mul] using congrArg Subtype.val hf12
  refine h.not_five_conj (f := (f : G)) (n := n) f.2 (fun h1' => hf1 (Subtype.ext h1'))
    (by rw [← Subgroup.coe_pow, hf5, Subgroup.coe_one]) fun x hx => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  have hxB : x ∈ Bt b z := by
    rcases hx with hx | hx | hx <;> rw [hx]
    · exact b_mem_Bt b z
    · exact zs_mem_Bt b z 0
    · exact zs_mem_Bt b z 1
  have hnx : n * x * n⁻¹ ∈ Bt b z := (Subgroup.mem_normalizer_iff.mp hn x).mp hxB
  refine ⟨hnx, comm_of_psi0 β hβ hfb hf0' hf12' hnx ?_⟩
  rcases hx with hx | hx | hx <;> rw [hx]
  · exact (hcol 0).symm.trans h0
  · exact (hcol 1).symm.trans h1
  · exact (hcol 2).symm.trans h2

end Five

end CFSG.StandardType.GGFF.Setting

end
