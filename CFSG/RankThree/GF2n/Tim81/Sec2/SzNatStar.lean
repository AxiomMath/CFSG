module

public import CFSG.Quasithin.Recognition.Stroth.Str83G2SzModule
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Conj

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open CFSG.Blueprint CFSG.LieType.Ree CFSG.Quasithin CFSG.Quasithin.H.Sz
open CFSG.Quasithin.Stroth
open CFSG.QuasithinUnique.Setup.X7
open scoped Matrix

variable {a : ℕ} {K : Type} [Field K] [CharP K 2] [Fintype K]

local instance (priority := 2000) zmod2AddCommGroupNatStar : AddCommGroup (ZMod 2) :=
  Ring.toAddCommGroup

private theorem eq_zero_of_mem_fixedSub_dual_of_natural
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (ha : 1 ≤ a) {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) ↥(suzukiGroup a K) M) {N : Submodule (ZMod 2) M} {c : ℕ}
    {φ : M →+ (Fin 4 → K)} (hsurj : Function.Surjective φ)
    (hker : φ.ker = N.toAddSubgroup)
    (heq : ∀ g m, φ (ρ g m) =
      (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c)) *ᵥ φ m)
    {L : Module.Dual (ZMod 2) M} (hLN : N ≤ LinearMap.ker L)
    (hLD : L ∈ fixedSub ρ.dual (suzukiT a K)) : L = 0 := by
  classical
  have hKunits : 1 < Fintype.card Kˣ := by
    rw [← Nat.card_eq_fintype_card, Nat.card_units, hK]
    have h8 : 8 ≤ 2 ^ (2 * a + 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨l, hl⟩ := Fintype.exists_ne_of_one_lt_card hKunits (1 : Kˣ)
  let D : Subgroup ↥(suzukiGroup a K) := suzukiT a K
  let d : ↥(suzukiGroup a K) := suzukiDElt a K l
  have hd : d ∈ D := suzukiDElt_mem_suzukiT a K l
  have hfixd : (ρ.dual d) L = L := mem_fixedSub.mp hLD d hd
  have hLinv : ∀ m : M, L (ρ d m) = L m := by
    intro m
    have h := congrArg (fun T : Module.Dual (ZMod 2) M => T m)
      (mem_fixedSub.mp hLD d⁻¹ (D.inv_mem hd))
    simpa [Representation.dual_apply, Module.Dual.transpose_apply] using h
  have hLN' : ∀ m ∈ N.toAddSubgroup, L m = 0 := fun m hm =>
    LinearMap.mem_ker.mp (hLN hm)
  let sec : (Fin 4 → K) → M := Function.surjInv hsurj
  have hsec : ∀ y, φ (sec y) = y := Function.surjInv_eq hsurj
  have hwell : ∀ (y : Fin 4 → K) (m : M), φ m = y → L m = L (sec y) := by
    intro y m hm
    have hmem : m - sec y ∈ N.toAddSubgroup := by
      rw [← hker]
      exact AddMonoidHom.mem_ker.mpr (by rw [map_sub, hm, hsec, sub_self])
    have h0 := hLN' _ hmem
    rw [map_sub] at h0
    exact sub_eq_zero.mp h0
  have hadd : ∀ y z : Fin 4 → K, L (sec (y + z)) = L (sec y) + L (sec z) := by
    intro y z
    have hmem : sec (y + z) - (sec y + sec z) ∈ N.toAddSubgroup := by
      rw [← hker]
      exact AddMonoidHom.mem_ker.mpr (by
        rw [map_sub, map_add, hsec, hsec, hsec, sub_self])
    have h0 := hLN' _ hmem
    rw [map_sub, map_add] at h0
    exact sub_eq_zero.mp h0
  let Lbar : (Fin 4 → K) →+ ZMod 2 :=
    AddMonoidHom.mk' (fun y => L (sec y)) hadd
  have hLbar : ∀ m : M, L m = Lbar (φ m) := fun m => hwell (φ m) m rfl
  have hmat : ∀ y : Fin 4 → K,
      Lbar (((suzukiD a l).map (· ^ 2 ^ c)) *ᵥ y) = Lbar y := by
    intro y
    have h1 : L (ρ d (sec y)) = L (sec y) := hLinv (sec y)
    have h2 : φ (ρ d (sec y)) = ((suzukiD a l).map (· ^ 2 ^ c)) *ᵥ y := by
      rw [heq d (sec y), coe_suzukiDElt, hsec]
    calc Lbar (((suzukiD a l).map (· ^ 2 ^ c)) *ᵥ y)
        = Lbar (φ (ρ d (sec y))) := by rw [h2]
      _ = L (ρ d (sec y)) := (hLbar _).symm
      _ = L (sec y) := h1
      _ = Lbar y := by rw [hLbar, hsec]
  have hMdiag : (suzukiD a l).map (· ^ 2 ^ c) =
      Matrix.diagonal (fun i : Fin 4 => (dEnt a l i) ^ 2 ^ c) := by
    rw [suzukiD_eq_diagonal, Matrix.diagonal_map]
    simp
  have hmul : ∀ (i : Fin 4) (x : K),
      ((suzukiD a l).map (· ^ 2 ^ c)) *ᵥ Pi.single i x =
        Pi.single i ((dEnt a l i) ^ 2 ^ c * x) := by
    intro i x
    rw [hMdiag]
    ext j
    by_cases h : j = i
    · subst h
      simp [Matrix.mulVec_diagonal]
    · simp [Matrix.mulVec_diagonal, Pi.single_apply, h]
  have hpsi : ∀ (i : Fin 4) (x : K),
      Lbar (Pi.single i ((dEnt a l i) ^ 2 ^ c * x)) = Lbar (Pi.single i x) := by
    intro i x
    have h := hmat (Pi.single i x)
    rwa [hmul i x] at h
  have hα : ∀ i : Fin 4, (dEnt a l i) ^ 2 ^ c ≠ 1 := by
    intro i h
    exact CFSG.Quasithin.Stroth.dEnt_ne_one hK hl i
      (iterateFrobenius_inj K 2 c (by simpa [iterateFrobenius_def] using h))
  let ψ : Fin 4 → K →+ ZMod 2 := fun i =>
    { toFun := fun x => Lbar (Pi.single i x)
      map_zero' := by simp
      map_add' := fun x y => by rw [Pi.single_add, map_add] }
  have hψzero : ∀ (i : Fin 4) (x : K), ψ i x = 0 := by
    intro i x
    have hne : (dEnt a l i) ^ 2 ^ c - 1 ≠ 0 := sub_ne_zero.mpr (hα i)
    let z : K := ((dEnt a l i) ^ 2 ^ c - 1)⁻¹ * x
    have hz : ((dEnt a l i) ^ 2 ^ c - 1) * z = x := by
      change ((dEnt a l i) ^ 2 ^ c - 1) *
        (((dEnt a l i) ^ 2 ^ c - 1)⁻¹ * x) = x
      rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    have h1 : ψ i ((dEnt a l i) ^ 2 ^ c * z) = ψ i z := hpsi i z
    calc ψ i x = ψ i (((dEnt a l i) ^ 2 ^ c - 1) * z) := by rw [hz]
      _ = ψ i ((dEnt a l i) ^ 2 ^ c * z - z) := by rw [sub_mul, one_mul]
      _ = ψ i ((dEnt a l i) ^ 2 ^ c * z) - ψ i z := map_sub (ψ i) _ _
      _ = 0 := sub_eq_zero.mpr h1
  have hLzero : Lbar = 0 := by
    refine AddMonoidHom.ext fun y => ?_
    have hy : y = ∑ i : Fin 4, Pi.single i (y i) := (Finset.univ_sum_single y).symm
    rw [hy, map_sum]
    exact Finset.sum_eq_zero fun i _ => hψzero i (y i)
  ext m
  rw [hLbar m, hLzero]
  rfl

theorem le_commSub_suzukiZ0_of_natural_quotient
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (ha : 1 ≤ a)
    {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : Representation (ZMod 2) ↥(suzukiGroup a K) M) (N : Submodule (ZMod 2) M)
    (hN : ∀ g, ∀ m ∈ N, ρ g m = m)
    (hnat : ∃ (c : ℕ) (φ : M →+ (Fin 4 → K)), Function.Surjective φ ∧
      φ.ker = N.toAddSubgroup ∧ ∀ g m,
        φ (ρ g m) = (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c)) *ᵥ φ m)
    (hM : commSub ρ ⊤ = ⊤) :
    N ≤ commSub ρ (suzukiZ0 a K) := by
  classical
  obtain ⟨c, φ, hsurj, hker, heq⟩ := hnat
  by_contra hnot
  obtain ⟨n, hnN, hnW⟩ := Set.not_subset.mp hnot
  obtain ⟨f, hfn, hfW⟩ := Submodule.exists_le_ker_of_notMem hnW
  let G : Type := ↥(suzukiGroup a K)
  let A : Subgroup G := suzukiZ0 a K
  let D : Subgroup G := suzukiT a K
  have hDA : D ≤ Subgroup.normalizer (A : Set G) := by
    exact (suzukiT_le_suzukiB a K).trans (suzukiB_le_normalizer_suzukiZ0 hK)
  have hfA : f ∈ fixedSub ρ.dual A := by
    rw [mem_fixedSub_dual, Submodule.mem_dualAnnihilator]
    intro w hw
    exact LinearMap.mem_ker.mp (hfW hw)
  haveI : Finite G := (suzuki_simple ha hK).1
  letI : Fintype D := Fintype.ofFinite D
  let πf : Module.Dual (ZMod 2) M := ∑ d : D, (ρ.dual (d : G)) f
  have hπD : πf ∈ fixedSub ρ.dual D := by
    rw [mem_fixedSub]
    intro d hd
    change (ρ.dual (d : G)) πf = πf
    rw [show πf = ∑ e : D, (ρ.dual (e : G)) f from rfl, map_sum]
    rw [show (∑ e : D, (ρ.dual (d : G)) ((ρ.dual (e : G)) f)) =
        ∑ e : D, (ρ.dual ((d : G) * (e : G))) f from by
      exact Finset.sum_congr rfl fun e _ => by
        rw [← Module.End.mul_apply, ← map_mul]]
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨d, hd⟩ : D))
      (fun e : D => (ρ.dual ((d : G) * (e : G))) f)
      (fun e : D => (ρ.dual (e : G)) f) (fun e => rfl)
  have hπA : πf ∈ fixedSub ρ.dual A := by
    rw [show πf = ∑ d : D, (ρ.dual (d : G)) f from rfl]
    apply Submodule.sum_mem
    intro d _
    have hdA : (d : G) ∈ Subgroup.normalizer (A : Set G) := hDA d.2
    have hmap : A.map (MulAut.conj (d : G)).toMonoidHom = A :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hdA
    have hmem : (ρ.dual (d : G)) f ∈ (fixedSub ρ.dual A).map (ρ.dual (d : G)) :=
      Submodule.mem_map_of_mem hfA
    rw [← fixedSub_map_conj (ρ := ρ.dual) (n := (d : G)) A, hmap] at hmem
    exact hmem
  have hπn : πf n ≠ 0 := by
    intro hπ0
    apply hfn
    have hterm : ∀ d : D, (ρ.dual (d : G)) f n = f n := by
      intro d
      rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]
      exact congrArg f (hN ((d : G)⁻¹) n hnN)
    have hcardD : Nat.card D = Nat.card Kˣ := by
      change Nat.card (suzukiT a K) = Nat.card Kˣ
      rw [(suzuki_borel_structure hK).2.2.1, Nat.card_units, hK]
    have hodd : Odd (Nat.card D) := by
      rw [hcardD]
      exact odd_card_units hK
    obtain ⟨k, hk⟩ := hodd
    have hcast : (Nat.card D : ZMod 2) = 1 := by
      rw [hk]
      push_cast
      rw [show (2 : ZMod 2) = 0 by decide, zero_mul, zero_add]
    have hsum : πf n = f n := by
      rw [show πf = ∑ d : D, (ρ.dual (d : G)) f from rfl, LinearMap.sum_apply]
      rw [Finset.sum_congr rfl fun d _ => hterm d]
      rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
      rw [← Nat.cast_smul_eq_nsmul (ZMod 2) (Nat.card D) (f n), hcast, one_smul]
    rw [hsum] at hπ0
    exact hπ0
  let g : Module.Dual (ZMod 2) M := (ρ.dual (suzukiWElt a K)) πf - πf
  have hgN : N ≤ LinearMap.ker g := by
    intro m hm
    rw [LinearMap.mem_ker]
    show ((ρ.dual (suzukiWElt a K)) πf - πf) m = 0
    rw [LinearMap.sub_apply, Representation.dual_apply, Module.Dual.transpose_apply,
      LinearMap.comp_apply, hN ((suzukiWElt a K)⁻¹) m hm, sub_self]
  have hgD : g ∈ fixedSub ρ.dual D := by
    rw [mem_fixedSub]
    intro d hd
    show (ρ.dual (d : G)) g = g
    rw [show g = (ρ.dual (suzukiWElt a K)) πf - πf from rfl, map_sub]
    have hdT : d ∈ suzukiT a K := by
      change d ∈ D
      exact hd
    have hd' : (suzukiWElt a K)⁻¹ * d * suzukiWElt a K ∈ D := by
      obtain ⟨l, rfl⟩ := mem_suzukiT_iff.1 hdT
      rw [suzukiWElt_inv, suzukiWElt_D_W hK l]
      exact suzukiDElt_mem_suzukiT a K l⁻¹
    have hconj : (ρ.dual (d : G)) ((ρ.dual (suzukiWElt a K)) πf) =
        (ρ.dual (suzukiWElt a K)) πf := by
      calc (ρ.dual (d : G)) ((ρ.dual (suzukiWElt a K)) πf)
          = (ρ.dual ((d : G) * suzukiWElt a K)) πf := by
              rw [← Module.End.mul_apply, ← map_mul]
        _ = (ρ.dual (suzukiWElt a K *
              ((suzukiWElt a K)⁻¹ * (d : G) * suzukiWElt a K))) πf := by
              rw [show (d : G) * suzukiWElt a K =
                suzukiWElt a K *
                  ((suzukiWElt a K)⁻¹ * (d : G) * suzukiWElt a K) by group]
        _ = (ρ.dual (suzukiWElt a K))
              ((ρ.dual ((suzukiWElt a K)⁻¹ * (d : G) * suzukiWElt a K)) πf) := by
              rw [map_mul, Module.End.mul_apply]
        _ = (ρ.dual (suzukiWElt a K)) πf := by
              rw [mem_fixedSub.mp hπD _ hd']
    rw [hconj, mem_fixedSub.mp hπD d hd]
  have hg0 : g = 0 :=
    eq_zero_of_mem_fixedSub_dual_of_natural hK ha ρ hsurj hker heq hgN hgD
  have hwfix : (ρ.dual (suzukiWElt a K)) πf = πf :=
    sub_eq_zero.mp (show (ρ.dual (suzukiWElt a K)) πf - πf = 0 from hg0)
  let H : Subgroup G :=
    { carrier := {g | (ρ.dual g) πf = πf}
      mul_mem' := fun {g h} hg hh => by
        show (ρ.dual (g * h)) πf = πf
        rw [map_mul, Module.End.mul_apply, hh, hg]
      one_mem' := by
        show (ρ.dual 1) πf = πf
        rw [map_one, Module.End.one_apply]
      inv_mem' := fun {g} hg => by
        show (ρ.dual g⁻¹) πf = πf
        calc (ρ.dual g⁻¹) πf = (ρ.dual g⁻¹) ((ρ.dual g) πf) := by rw [hg]
          _ = (ρ.dual (g⁻¹ * g)) πf := by rw [map_mul, Module.End.mul_apply]
          _ = πf := by rw [inv_mul_cancel, map_one, Module.End.one_apply] }
  have hA : A ≤ H := fun a ha => mem_fixedSub.mp hπA a ha
  have hwH : suzukiWElt a K ∈ H := hwfix
  have htop : H = ⊤ := suzuki_eq_top_of_suzukiZ0_le_of_W_mem hK ha hA hwH
  have hπtop : πf ∈ fixedSub ρ.dual ⊤ := by
    rw [mem_fixedSub]
    intro h _
    have hh : h ∈ H := by rw [htop]; exact Subgroup.mem_top h
    exact hh
  have hmem : πf ∈ (commSub ρ ⊤).dualAnnihilator := by
    rw [← fixedSub_dual_eq]
    exact hπtop
  rw [hM] at hmem
  have hzero : πf = 0 := by
    have h := (Submodule.mem_dualAnnihilator πf).mp hmem
    ext m
    exact h m (Submodule.mem_top)
  exact hπn (by simp [hzero])

end CFSG.RankThree.GF2n.Tim81.Sec2

end
