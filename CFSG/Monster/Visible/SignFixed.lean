module

public import CFSG.Monster.ScalarKernel
public import CFSG.Monster.Lifts.SignLift
public import CFSG.Monster.SpinLattice.Lambda
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSG.Monster.CodeRadical

public noncomputable section

namespace CFSG.Monster.Visible

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.ScalarKernel
  CFSG.Monster.SpinLattice Matrix

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem bitLift_zero' : bitLift (0 : ZMod 2) = 0 := rfl

@[expose] def maskVec (a : Fin 24 → ZMod 2) (u : Fin 24 → ℤ) : Fin 24 → ℤ :=
  fun i => bitLift (a i) * u i

@[expose] def signVec (a : Fin 24 → ZMod 2) (u : Fin 24 → ℤ) : Fin 24 → ℤ :=
  u - (2 : ℤ) • maskVec a u

theorem maskVec_apply (a : Fin 24 → ZMod 2) (u : Fin 24 → ℤ) (i : Fin 24) :
    maskVec a u i = bitLift (a i) * u i := rfl

theorem signVec_apply (a : Fin 24 → ZMod 2) (u : Fin 24 → ℤ) (i : Fin 24) :
    signVec a u i = u i - 2 * (bitLift (a i) * u i) := rfl

theorem maskVec_sub (a : Fin 24 → ZMod 2) (u v : Fin 24 → ℤ) :
    maskVec a (u - v) = maskVec a u - maskVec a v := by
  funext i
  simp only [maskVec_apply, Pi.sub_apply]
  ring

private theorem sgn_eq_bitLift (t : ZMod 2) : sgn t = 1 - 2 * ((bitLift t : ℤ) : ℚ) := by
  rcases zmod2_cases t with rfl | rfl
  · rw [sgn_zero, bitLift_zero']
    norm_num
  · rw [show sgn 1 = -1 from rfl, bitLift_one]
    norm_num

theorem ratVec_vecMul_gmat (a : C) (u : Fin 24 → ℤ) :
    ratVec u ᵥ* gmat a = ratVec (signVec a u) := by
  funext i
  rw [gmat, vecMul_diagonal, ratVec_apply, ratVec_apply, signVec_apply, sgn_eq_bitLift]
  push_cast
  ring

theorem sum_maskVec_emod_four {a : Fin 24 → ZMod 2} (ha : a ∈ C) {u : Fin 24 → ℤ}
    (hu : u ∈ codeLattice C) : (∑ i, maskVec a u i) % 4 = 0 := by
  obtain ⟨m, hm, d, hd, hud, -⟩ := hu
  have hk : ∀ i, u i = m + 2 * bitLift (d i) + 4 * ((u i - m - 2 * bitLift (d i)) / 4) := by
    intro i
    have h := hud i
    unfold Int.ModEq at h
    omega
  have e : ∑ i, maskVec a u i = m * ∑ i, bitLift (a i) +
      2 * ∑ i, bitLift (a i) * bitLift (d i) +
      4 * ∑ i, bitLift (a i) * ((u i - m - 2 * bitLift (d i)) / 4) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [maskVec_apply]
    conv_lhs => rw [hk i]
    ring
  have hw : (∑ i, bitLift (a i)) % 4 = 0 := weight_mod_four ha
  have hdot : (∑ i, bitLift (a i) * bitLift (d i)) % 2 = 0 := by
    have h1 : ((∑ i, bitLift (a i) * bitLift (d i) : ℤ) : ZMod 2) = a ⬝ᵥ d := by
      push_cast
      simp only [bitLift_cast]
      rfl
    rw [← bitLift_intCast, h1, dotProduct_eq_zero ha hd]
    rfl
  rw [e]
  rcases hm with rfl | rfl <;> omega

theorem two_maskVec_mem {a : Fin 24 → ZMod 2} (ha : a ∈ C) {u : Fin 24 → ℤ}
    (hu : u ∈ codeLattice C) : (2 : ℤ) • maskVec a u ∈ codeLattice C := by
  have h4 := sum_maskVec_emod_four ha hu
  obtain ⟨m, -, d, -, hud, -⟩ := hu
  refine mem_of_even (y := maskVec a u) (fun i => rfl) ?_ ?_
  · have e : (fun i => (maskVec a u i : ZMod 2)) = (m : ZMod 2) • a := by
      funext i
      have h := hud i
      have hui : ((u i : ℤ) : ZMod 2) = (m : ZMod 2) := by
        rw [ZMod.intCast_eq_intCast_iff']
        unfold Int.ModEq at h
        push_cast
        omega
      simp only [maskVec_apply, Int.cast_mul, bitLift_cast, hui, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact C.smul_mem _ ha
  · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    omega

theorem signVec_mem {a : Fin 24 → ZMod 2} (ha : a ∈ C) {u : Fin 24 → ℤ}
    (hu : u ∈ codeLattice C) : signVec a u ∈ codeLattice C :=
  (codeLatticeSubgroup allOnes_mem_C).sub_mem hu (two_maskVec_mem ha hu)

theorem image_latticeQ_gmat (a : C) : (fun x => x ᵥ* gmat a) '' latticeQ = latticeQ := by
  refine Set.Subset.antisymm ?_ fun x hx => ?_
  · rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨signVec a u, signVec_mem a.2 hu, (ratVec_vecMul_gmat a u).symm⟩
  · obtain ⟨u, hu, rfl⟩ := hx
    refine ⟨ratVec (signVec a u), ⟨_, signVec_mem a.2 hu, rfl⟩, ?_⟩
    show ratVec (signVec a u) ᵥ* gmat a = ratVec u
    rw [← ratVec_vecMul_gmat, vecMul_vecMul, gmat_mul_self, vecMul_one]

theorem gU_mem_latticeO (a : C) : gU a ∈ latticeO :=
  ⟨(mem_orthogonalGroup_iff _ _).2 (gmat_mul_transpose_self a), image_latticeQ_gmat a⟩

@[expose] def gO (a : C) : latticeO := ⟨gU a, gU_mem_latticeO a⟩

theorem coe_gO (a : C) : (gO a : GL (Fin 24) ℚ) = gU a := rfl

theorem mat_gO (a : C) : mat (gO a) = gmat a := rfl

theorem gmat_add (a b : C) : gmat (a + b) = gmat a * gmat b := by
  rw [gmat, gmat, gmat, diagonal_mul_diagonal]
  congr 1
  funext i
  rw [Submodule.coe_add, Pi.add_apply, sgn_add]

theorem gmat_zero : gmat 0 = 1 := by
  rw [gmat, ← diagonal_one]
  exact congrArg diagonal (funext fun _ => sgn_zero)

theorem gO_add (a b : C) : gO (a + b) = gO a * gO b :=
  mat_injective (by rw [mat_mul, mat_gO, mat_gO, mat_gO, gmat_add])

theorem gO_zero : gO 0 = 1 := mat_injective (by rw [mat_gO, mat_one, gmat_zero])

theorem gO_comm (a b : C) : gO a * gO b = gO b * gO a := by
  rw [← gO_add, ← gO_add, add_comm]

theorem latVec_gO (a : C) {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) :
    latVec (mat (gO a)) u = signVec a u :=
  ratVec_injective ((latVec_spec (gO a) hu).2.trans (ratVec_vecMul_gmat a u))

theorem modTwoEnd_gO_cls (a : C) {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) :
    modTwoEnd (gO a) (cls u hu) = cls (signVec a u) (signVec_mem a.2 hu) :=
  (modTwoEnd_mk (gO a) ⟨u, hu⟩).trans
    (congrArg Submodule.Quotient.mk (Subtype.ext (latVec_gO a hu)))

theorem cls_two_smul_eq_zero_iff {w : Fin 24 → ℤ} (h : (2 : ℤ) • w ∈ codeLattice C) :
    cls ((2 : ℤ) • w) h = 0 ↔ w ∈ codeLattice C := by
  refine ⟨fun h0 => ?_, fun hw => cls_two_smul hw h⟩
  rw [cls, Submodule.Quotient.mk_eq_zero, mem_two_range_iff] at h0
  obtain ⟨w', hw'⟩ := h0
  have e : (w' : Fin 24 → ℤ) = w := by
    funext i
    have hi := congrFun hw' i
    change 2 * (w' : Fin 24 → ℤ) i = 2 * w i at hi
    omega
  exact e ▸ w'.2

theorem cls_signVec_eq_iff {a : Fin 24 → ZMod 2} (ha : a ∈ C) {u : Fin 24 → ℤ}
    (hu : u ∈ codeLattice C) :
    cls (signVec a u) (signVec_mem ha hu) = cls u hu ↔ maskVec a u ∈ codeLattice C := by
  have e : cls u hu = cls (signVec a u) (signVec_mem ha hu) +
      cls ((2 : ℤ) • maskVec a u) (two_maskVec_mem ha hu) := by
    rw [cls_add]
    exact cls_congr hu (sub_add_cancel u _).symm
  rw [e, left_eq_add, cls_two_smul_eq_zero_iff]

theorem modTwoEnd_gO_cls_eq_iff (a : C) {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) :
    modTwoEnd (gO a) (cls u hu) = cls u hu ↔ maskVec a u ∈ codeLattice C := by
  rw [modTwoEnd_gO_cls]
  exact cls_signVec_eq_iff a.2 hu

@[expose] def twoΩ : Fin 24 → ℤ := fun _ => 2

theorem twoΩ_apply (i : Fin 24) : twoΩ i = 2 := rfl

theorem twoΩ_mem : twoΩ ∈ codeLattice C := by
  refine mem_of_even (y := fun _ => 1) (fun _ => rfl) ?_ ?_
  · show (fun _ => ((1 : ℤ) : ZMod 2)) ∈ C
    rw [Int.cast_one]
    exact Ω_mem_C
  · simp [twoΩ_apply]

@[expose] def twoΩCls : L2 := cls twoΩ twoΩ_mem

theorem twoΩCls_eq : twoΩCls = cls twoΩ twoΩ_mem := rfl

theorem maskVec_twoΩ_mem {a : Fin 24 → ZMod 2} (ha : a ∈ C) :
    maskVec a twoΩ ∈ codeLattice C := by
  have e : maskVec a twoΩ = fun i => 2 * bitLift (a i) := by
    funext i
    rw [maskVec_apply, twoΩ_apply, mul_comm]
  rw [e]
  exact two_bitLift_mem weight_mod_four' ha

theorem twoΩCls_ne_zero : twoΩCls ≠ 0 := by
  intro h
  have h2 : twoΩ = (2 : ℤ) • (fun _ => (1 : ℤ)) := by
    funext i
    rfl
  have hΩ : (fun _ => (1 : ℤ)) ∈ codeLattice C :=
    (cls_two_smul_eq_zero_iff (h2 ▸ twoΩ_mem)).1 ((cls_congr twoΩ_mem h2).symm.trans h)
  obtain ⟨m, hm, d, -, hd, hs⟩ := hΩ
  have h0 : (1 : ℤ) ≡ m + 2 * bitLift (d 0) [ZMOD 4] := hd 0
  have hs' : (24 : ℤ) ≡ 4 * m [ZMOD 8] := by
    have e : ∑ _i : Fin 24, (1 : ℤ) = 24 := by simp
    rw [← e]
    exact hs
  have hb := bitLift_zero_or_one (d 0)
  unfold Int.ModEq at h0 hs'
  rcases hm with rfl | rfl <;> omega

theorem sum_emod_eight_of_four_dvd {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C)
    (h4 : ∀ i, u i % 4 = 0) : (∑ i, u i) % 8 = 0 := by
  obtain ⟨m, hm, d, -, hud, hus⟩ := hu
  have h0 := hud 0
  have h00 := h4 0
  have hb := bitLift_zero_or_one (d 0)
  unfold Int.ModEq at h0 hus
  rcases hm with rfl | rfl <;> omega

theorem eq_zero_or_eq_twoΩCls_of_four_dvd {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C)
    (h4 : ∀ i, u i % 4 = 0) (hfix : ∀ a ∈ C, maskVec a u ∈ codeLattice C) :
    cls u hu = 0 ∨ cls u hu = twoΩCls := by
  have hsum := sum_emod_eight_of_four_dvd hu h4
  set k : Fin 24 → ℤ := fun i => u i / 4 with hk
  have huk : ∀ i, u i = 4 * k i := fun i => by
    have := h4 i
    simp only [hk]
    omega
  have hsumk : ∑ i, u i = 4 * ∑ i, k i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => huk i
  have hkC : (fun i => (k i : ZMod 2)) ∈ C := by
    rw [mem_C_iff_forall_dotProduct]
    intro a ha
    have hm := hfix a ha
    have hm4 : ∀ i, maskVec a u i % 4 = 0 := fun i => by
      rw [maskVec_apply, huk i]
      rcases bitLift_zero_or_one (a i) with h | h <;> rw [h] <;> omega
    have hs := sum_emod_eight_of_four_dvd hm hm4
    have e : ∑ i, maskVec a u i = 4 * ∑ i, bitLift (a i) * k i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [maskVec_apply, huk i]
      ring
    have hev : (∑ i, bitLift (a i) * k i) % 2 = 0 := by omega
    have hcast : ((∑ i, bitLift (a i) * k i : ℤ) : ZMod 2) =
        (fun i => (k i : ZMod 2)) ⬝ᵥ a := by
      push_cast
      simp only [bitLift_cast]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [← hcast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.dvd_of_emod_eq_zero hev
  have hkres : ∀ i, 2 * k i ≡ 0 + 2 * bitLift ((k i : ℤ) : ZMod 2) [ZMOD 4] := fun i => by
    rw [bitLift_intCast]
    unfold Int.ModEq
    omega
  have hk2 : (∑ i, k i) % 2 = 0 := by omega
  rcases (show (∑ i, k i) % 4 = 0 ∨ (∑ i, k i) % 4 = 2 by omega) with h0 | h2
  ·
    left
    have hw : (2 : ℤ) • k ∈ codeLattice C := by
      refine ⟨0, .inl rfl, _, hkC, fun i => hkres i, ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_zero]
      unfold Int.ModEq
      omega
    have e : u = (2 : ℤ) • ((2 : ℤ) • k) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [huk i]
      ring
    rw [cls_congr hu e]
    exact cls_two_smul hw _
  ·
    right
    set e₀ : Fin 24 → ℤ := fun j => if j = 0 then 1 else 0 with he₀
    have hsum₀ : ∑ j, e₀ j = 1 := by simp [he₀]
    have hw : (2 : ℤ) • k - (4 : ℤ) • e₀ ∈ codeLattice C := by
      refine ⟨0, .inl rfl, _, hkC, fun i => ?_, ?_⟩
      · have h := hkres i
        unfold Int.ModEq at h ⊢
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, he₀]
        split_ifs <;> omega
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
          ← Finset.mul_sum, hsum₀, mul_zero]
        unfold Int.ModEq
        omega
    have h8 : (8 : ℤ) • e₀ ∈ codeLattice C := smul_eight_mem_codeLattice e₀
    have h2w : (2 : ℤ) • ((2 : ℤ) • k - (4 : ℤ) • e₀) ∈ codeLattice C :=
      (codeLatticeSubgroup allOnes_mem_C).zsmul_mem hw 2
    have hlam : (2 : ℤ) • lam 0 ∈ codeLattice C :=
      (codeLatticeSubgroup allOnes_mem_C).zsmul_mem (lam_mem 0) 2
    have e1 : u = (2 : ℤ) • ((2 : ℤ) • k - (4 : ℤ) • e₀) + (8 : ℤ) • e₀ := by
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [huk i]
      ring
    have e2 : twoΩ = (8 : ℤ) • e₀ + (2 : ℤ) • lam 0 := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, twoΩ_apply, lam, he₀]
      ring
    rw [cls_congr hu e1, ← cls_add h2w h8, cls_two_smul hw h2w, zero_add, twoΩCls_eq,
      cls_congr twoΩ_mem e2, ← cls_add h8 hlam, cls_two_smul (lam_mem 0) hlam, add_zero]

theorem eq_zero_or_eq_twoΩCls {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C)
    (hfix : ∀ a ∈ C, maskVec a u ∈ codeLattice C) : cls u hu = 0 ∨ cls u hu = twoΩCls := by
  have hu' := hu
  obtain ⟨m, hm, d, hd, hud, -⟩ := hu'
  have hB0 : B 0 0 = 0 := by decide
  have hB1 : B 0 1 = 1 := by decide
  have hm0 : m = 0 := by
    obtain ⟨m', hm', d', -, hd'u, -⟩ := hfix (B 0) (B_mem_C 0)
    have h0 := hd'u 0
    have h1 := hd'u 1
    have h1' := hud 1
    rw [maskVec_apply, hB0, bitLift_zero'] at h0
    rw [maskVec_apply, hB1, bitLift_one] at h1
    have hb0 := bitLift_zero_or_one (d' 0)
    have hb1 := bitLift_zero_or_one (d' 1)
    have hb := bitLift_zero_or_one (d 1)
    unfold Int.ModEq at h0 h1 h1'
    rcases hm with rfl | rfl <;> rcases hm' with rfl | rfl <;> omega
  subst hm0
  have hmul : ∀ a ∈ C, a * d ∈ C := by
    intro a ha
    obtain ⟨m', hm', d', hd', hd'u, -⟩ := hfix a ha
    have hm'0 : m' = 0 := by
      have h0 := hd'u 0
      have h0' := hud 0
      have hb := bitLift_zero_or_one (d 0)
      have hb' := bitLift_zero_or_one (d' 0)
      rw [maskVec_apply] at h0
      unfold Int.ModEq at h0 h0'
      rcases bitLift_zero_or_one (a 0) with hc | hc <;> rw [hc] at h0 <;>
        rcases hm' with rfl | rfl <;> omega
    subst hm'0
    have e : d' = a * d := by
      funext i
      have h1 := hd'u i
      have h2 := hud i
      have hb := bitLift_zero_or_one (d i)
      have hb' := bitLift_zero_or_one (d' i)
      rw [maskVec_apply] at h1
      unfold Int.ModEq at h1 h2
      have key : bitLift (d' i) = bitLift (a i) * bitLift (d i) := by
        rcases bitLift_zero_or_one (a i) with hc | hc <;> rw [hc] at h1 ⊢ <;> omega
      rw [Pi.mul_apply, ← bitLift_cast (d' i), key, ← bitLift_mul, bitLift_cast]
    rw [← e]
    exact hd'
  rcases (mul_mem_C_iff hd).1 hmul with rfl | rfl
  ·
    refine eq_zero_or_eq_twoΩCls_of_four_dvd hu (fun i => ?_) hfix
    have h := hud i
    rw [Pi.zero_apply, bitLift_zero'] at h
    unfold Int.ModEq at h
    omega
  ·
    have hu2 : u - twoΩ ∈ codeLattice C :=
      (codeLatticeSubgroup allOnes_mem_C).sub_mem hu twoΩ_mem
    have h4 : ∀ i, (u - twoΩ) i % 4 = 0 := fun i => by
      have h := hud i
      rw [show bitLift (Ω i) = 1 from rfl] at h
      unfold Int.ModEq at h
      simp only [Pi.sub_apply, twoΩ_apply]
      omega
    have hfix2 : ∀ a ∈ C, maskVec a (u - twoΩ) ∈ codeLattice C := fun a ha => by
      rw [maskVec_sub]
      exact (codeLatticeSubgroup allOnes_mem_C).sub_mem (hfix a ha) (maskVec_twoΩ_mem ha)
    have e : cls u hu = cls (u - twoΩ) hu2 + twoΩCls := by
      rw [twoΩCls_eq, cls_add]
      exact cls_congr hu (sub_add_cancel u twoΩ).symm
    rcases eq_zero_or_eq_twoΩCls_of_four_dvd hu2 h4 hfix2 with h | h
    · right
      rw [e, h, zero_add]
    · left
      rw [e, h, ZModModule.add_self]

@[expose] def signHom : Multiplicative C →* LinearMap.GeneralLinearGroup (ZMod 2) L2 where
  toFun a := modTwoUnit (gO (Multiplicative.toAdd a))
  map_one' := Units.ext (by
    show modTwoEnd (gO 0) = 1
    rw [gO_zero, modTwoEnd_one])
  map_mul' a b := Units.ext (by
    show modTwoEnd (gO (Multiplicative.toAdd a + Multiplicative.toAdd b)) =
      modTwoEnd (gO (Multiplicative.toAdd a)) * modTwoEnd (gO (Multiplicative.toAdd b))
    rw [gO_add, gO_comm, modTwoEnd_mul])

theorem signHom_apply (a : C) : signHom (Multiplicative.ofAdd a) = modTwoUnit (gO a) := rfl

def Esign : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) L2) := signHom.range

theorem mem_Esign {f : LinearMap.GeneralLinearGroup (ZMod 2) L2} :
    f ∈ Esign ↔ ∃ a : C, modTwoUnit (gO a) = f :=
  ⟨fun ⟨a, ha⟩ => ⟨Multiplicative.toAdd a, ha⟩, fun ⟨a, ha⟩ => ⟨Multiplicative.ofAdd a, ha⟩⟩

theorem coe_modTwoUnit (g : latticeO) :
    ((modTwoUnit g : LinearMap.GeneralLinearGroup (ZMod 2) L2) : Module.End (ZMod 2) L2) =
      modTwoEnd g := rfl

private theorem multiplicative_sq (a : Multiplicative C) : a ^ 2 = 1 := by
  rw [pow_two, ← ofAdd_toAdd a, ← ofAdd_add, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl,
    zero_smul, ofAdd_zero]

theorem mul_comm_of_mem_Esign {f f' : LinearMap.GeneralLinearGroup (ZMod 2) L2} (hf : f ∈ Esign)
    (hf' : f' ∈ Esign) : f * f' = f' * f := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hf'
  rw [← map_mul, ← map_mul, mul_comm]

theorem sq_eq_one_of_mem_Esign {f : LinearMap.GeneralLinearGroup (ZMod 2) L2} (hf : f ∈ Esign) :
    f ^ 2 = 1 := by
  obtain ⟨a, rfl⟩ := hf
  rw [← map_pow, multiplicative_sq, map_one]

theorem isElementaryAbelian_Esign : IsElementaryAbelian 2 Esign where
  is_comm := ⟨fun x y => by
    obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha, ← hb, ← map_mul, ← map_mul, mul_comm]⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
    obtain ⟨a, ha⟩ := x.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← ha, ← map_pow, multiplicative_sq, map_one, Subgroup.coe_one]

def signFixed : Submodule (ZMod 2) L2 where
  carrier := {v | ∀ a : C, modTwoEnd (gO a) v = v}
  add_mem' hv hw a := by rw [map_add, hv a, hw a]
  zero_mem' a := map_zero _
  smul_mem' c v hv a := by rw [map_smul, hv a]

theorem mem_signFixed {v : L2} : v ∈ signFixed ↔ ∀ a : C, modTwoEnd (gO a) v = v := Iff.rfl

theorem mem_signFixed_iff_Esign {v : L2} :
    v ∈ signFixed ↔ ∀ f ∈ Esign, (f : Module.End (ZMod 2) L2) v = v := by
  refine ⟨fun hv f hf => ?_, fun h a => h _ (mem_Esign.2 ⟨a, rfl⟩)⟩
  obtain ⟨a, rfl⟩ := mem_Esign.1 hf
  exact hv a

theorem twoΩCls_mem_signFixed : twoΩCls ∈ signFixed := fun a =>
  (modTwoEnd_gO_cls_eq_iff a twoΩ_mem).2 (maskVec_twoΩ_mem a.2)

theorem signFixed_eq_span : signFixed = (ZMod 2) ∙ twoΩCls := by
  refine le_antisymm (fun v hv => ?_)
    ((Submodule.span_singleton_le_iff_mem _ _).2 twoΩCls_mem_signFixed)
  induction v using Submodule.Quotient.induction_on with
  | H u =>
    have hfix : ∀ a ∈ C, maskVec a u ∈ codeLattice C := fun a ha =>
      (modTwoEnd_gO_cls_eq_iff ⟨a, ha⟩ u.2).1 (hv ⟨a, ha⟩)
    show cls (u : Fin 24 → ℤ) u.2 ∈ (ZMod 2) ∙ twoΩCls
    rcases eq_zero_or_eq_twoΩCls u.2 hfix with h | h
    · rw [h]
      exact Submodule.zero_mem _
    · rw [h]
      exact Submodule.mem_span_singleton_self _

theorem finrank_signFixed : Module.finrank (ZMod 2) signFixed = 1 := by
  rw [signFixed_eq_span]
  exact finrank_span_singleton twoΩCls_ne_zero

theorem code_sign_common_fixed_line :
    (∀ a : C, gU a ∈ latticeO) ∧
    (∀ (a : C) (u : Fin 24 → ℤ) (hu : u ∈ codeLattice C),
      ratVec u ᵥ* gmat a = ratVec (fun i => u i - 2 * (bitLift ((a : Fin 24 → ZMod 2) i) * u i)) ∧
      modTwoEnd (gO a) (cls u hu) = cls (signVec a u) (signVec_mem a.2 hu)) ∧
    (∀ f : LinearMap.GeneralLinearGroup (ZMod 2) L2, f ∈ Esign ↔ ∃ a : C, modTwoUnit (gO a) = f) ∧
    (∀ a : C, ((modTwoUnit (gO a) : LinearMap.GeneralLinearGroup (ZMod 2) L2) :
      Module.End (ZMod 2) L2) = modTwoEnd (gO a)) ∧
    (∀ f ∈ Esign, ∀ f' ∈ Esign, f * f' = f' * f) ∧ (∀ f ∈ Esign, f ^ 2 = 1) ∧
    IsElementaryAbelian 2 Esign ∧
    (∀ v : L2, v ∈ signFixed ↔ ∀ f ∈ Esign, (f : Module.End (ZMod 2) L2) v = v) ∧
    (∀ v : L2, v ∈ signFixed ↔ ∀ a : C, modTwoEnd (gO a) v = v) ∧
    twoΩCls = cls (fun _ => 2) twoΩ_mem ∧
    signFixed = (ZMod 2) ∙ twoΩCls ∧ twoΩCls ≠ 0 ∧ Module.finrank (ZMod 2) signFixed = 1 :=
  ⟨gU_mem_latticeO, fun a u hu => ⟨ratVec_vecMul_gmat a u, modTwoEnd_gO_cls a hu⟩,
    fun _ => mem_Esign, fun _ => rfl, fun _ hf _ hf' => mul_comm_of_mem_Esign hf hf',
    fun _ hf => sq_eq_one_of_mem_Esign hf, isElementaryAbelian_Esign,
    fun _ => mem_signFixed_iff_Esign, fun _ => mem_signFixed, rfl, signFixed_eq_span,
    twoΩCls_ne_zero, finrank_signFixed⟩

end CFSG.Monster.Visible
