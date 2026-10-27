module

public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.Defs
public import Certificates.Certificate113
import CFSG.GroupTheory.CentralSylowComplement
import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.Involution

public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

open CFSG.Timmesfeld.Bridge.Asc72

variable {X : Type} [Group X] [Finite X] {F : Set X}

theorem exists_odd_complement_le_oddCore
    (hQ : CFSG.pCore 2 X ≤ Subgroup.center X) :
    ∃ W : Subgroup X, W ≤ CFSG.oddCore X ∧ W.Normal ∧
      CFSG.pCore 2 X ⊓ W = ⊥ ∧
      (∀ x ∈ EightOne.twoOddCore X, x ∈ W ↔ Odd (orderOf x)) ∧
      ∀ x ∈ EightOne.twoOddCore X, ∃ q ∈ CFSG.pCore 2 X, ∃ o ∈ W, x = q * o := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQX : CFSG.pCore 2 X ≤ EightOne.twoOddCore X := pCore_le_twoOddCore X
  have hcent : ∀ x ∈ EightOne.twoOddCore X, ∀ q ∈ CFSG.pCore 2 X, x * q = q * x := by
    intro x _ q hq
    exact Subgroup.mem_center_iff.mp (hQ hq) x
  have hidx : ¬ 2 ∣ (CFSG.pCore 2 X).relIndex (EightOne.twoOddCore X) := by
    rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 X), Subgroup.relIndex_ker]
    rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)
      (CFSG.oddCore (X ⧸ CFSG.pCore 2 X))]
    exact (CFSG.ABGLocalTools.odd_card_oddCore
      (H := X ⧸ CFSG.pCore 2 X)).not_two_dvd_nat
  obtain ⟨W, hWK, hWchar, hQinfW, hdecomp⟩ :=
    CFSG.GroupTheory.exists_complement_of_central_sylow_two hQX CFSG.pCore_isPGroup hcent hidx
  have hWn : W.Normal := by
    refine ⟨fun w hw g => ?_⟩
    have hgK : g * w * g⁻¹ ∈ EightOne.twoOddCore X :=
      (Subgroup.Normal.comap (CFSG.oddCore_normal (G := X ⧸ CFSG.pCore 2 X))
        (QuotientGroup.mk' (CFSG.pCore 2 X))).conj_mem w (hWK hw) g
    rw [hWchar _ hgK]
    have hord : orderOf (g * w * g⁻¹) = orderOf w := by
      simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj g) w
    rw [hord]
    exact (hWchar w (hWK hw)).mp hw
  have hWodd : Odd (Nat.card W) := by
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := W) 2 (even_iff_two_dvd.mp hodd)
    have hwW : ((w : W) : X) ∈ W := w.2
    have hwo : Odd (orderOf ((w : W) : X)) :=
      (hWchar _ (hWK hwW)).mp hwW
    rw [Subgroup.orderOf_coe, hw] at hwo
    exact (by decide : ¬ Odd 2) hwo
  exact ⟨W, CFSG.ABGLocalTools.le_oddCore_of_normal hWn hWodd, hWn, hQinfW, hWchar, hdecomp⟩

theorem oddCore_le_twoOddCore (X : Type) [Group X] [Finite X] :
    CFSG.oddCore X ≤ EightOne.twoOddCore X := by
  have hOodd : Odd (Nat.card (CFSG.oddCore X)) := CFSG.ABGLocalTools.odd_card_oddCore
  have hmap : (CFSG.oddCore X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) ≤
      CFSG.oddCore (X ⧸ CFSG.pCore 2 X) := by
    apply CFSG.ABGLocalTools.le_oddCore_of_normal
    · exact (CFSG.oddCore_normal (G := X)).map _
        (QuotientGroup.mk'_surjective (CFSG.pCore 2 X))
    · exact hOodd.of_dvd_nat (Subgroup.card_map_dvd _ _)
  intro o ho
  show o ∈ (CFSG.oddCore (X ⧸ CFSG.pCore 2 X)).comap
    (QuotientGroup.mk' (CFSG.pCore 2 X))
  rw [Subgroup.mem_comap, QuotientGroup.mk'_apply]
  exact hmap (Subgroup.mem_map_of_mem _ ho)

private theorem exists_pCore_map_eq {W : Subgroup X}
    (hdecomp : ∀ x ∈ EightOne.twoOddCore X, ∃ q ∈ CFSG.pCore 2 X, ∃ o ∈ W, x = q * o)
    (hWO : W ≤ CFSG.oddCore X) {k : X} (hk : k ∈ EightOne.twoOddCore X) :
    ∃ q ∈ CFSG.pCore 2 X,
      QuotientGroup.mk' (CFSG.oddCore X) k = QuotientGroup.mk' (CFSG.oddCore X) q := by
  obtain ⟨q, hq, o, ho, rfl⟩ := hdecomp k hk
  refine ⟨q, hq, ?_⟩
  rw [map_mul, show QuotientGroup.mk' (CFSG.oddCore X) o = 1 from
    (QuotientGroup.eq_one_iff o).mpr (hWO ho), mul_one]

private theorem mul_conj_mem_twoOddCore {U : Type} [Group U]
    (hS : Setup X F) {ρ : X →* Multiplicative (ZMod 2) × U}
    (hρker : ρ.ker = EightOne.twoOddCore X) {x : X} (hx2 : (ρ x).2 = 1)
    {f : X} (hf : f ∈ F) :
    f * (x * f * x⁻¹) ∈ EightOne.twoOddCore X := by
  have hρxcent : ∀ z : Multiplicative (ZMod 2) × U, ρ x * z = z * ρ x := by
    intro z
    ext
    · simp [mul_comm]
    · simp [hx2]
  have hf2 : ρ f * ρ f = 1 := by
    rw [← map_mul, hS.oddT.mul_self_eq_one hf, map_one]
  rw [← hρker, MonoidHom.mem_ker, map_mul]
  have h1 : ρ (x * f * x⁻¹) = ρ f := by
    rw [map_mul, map_mul, map_inv, hρxcent (ρ f)]
    have hxinv : ρ x * (ρ x)⁻¹ = 1 := mul_inv_cancel (ρ x)
    rw [mul_assoc, hxinv, mul_one]
  rw [h1, hf2]

private theorem map_conj_eq_of_odd {U : Type} [Group U] {W : Subgroup X}
    (hS : Setup X F) (hWO : W ≤ CFSG.oddCore X)
    (hWchar : ∀ x ∈ EightOne.twoOddCore X, x ∈ W ↔ Odd (orderOf x))
    {ρ : X →* Multiplicative (ZMod 2) × U}
    (hρker : ρ.ker = EightOne.twoOddCore X) {x : X} (hx2 : (ρ x).2 = 1)
    {f : X} (hf : f ∈ F) (hcodd : Odd (orderOf (f * (x * f * x⁻¹)))) :
    QuotientGroup.mk' (CFSG.oddCore X) (x * f * x⁻¹) =
      QuotientGroup.mk' (CFSG.oddCore X) f := by
  have hcK := mul_conj_mem_twoOddCore hS hρker hx2 hf
  have hcO : f * (x * f * x⁻¹) ∈ CFSG.oddCore X :=
    hWO ((hWchar _ hcK).mpr hcodd)
  have hπc : QuotientGroup.mk' (CFSG.oddCore X) (f * (x * f * x⁻¹)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hcO
  have h : QuotientGroup.mk' (CFSG.oddCore X) f *
      QuotientGroup.mk' (CFSG.oddCore X) (x * f * x⁻¹) = 1 := by
    rw [← map_mul]; exact hπc
  have hfπ2 : QuotientGroup.mk' (CFSG.oddCore X) f *
      QuotientGroup.mk' (CFSG.oddCore X) f = 1 := by
    rw [← map_mul, hS.oddT.mul_self_eq_one hf, map_one]
  calc QuotientGroup.mk' (CFSG.oddCore X) (x * f * x⁻¹) =
        (QuotientGroup.mk' (CFSG.oddCore X) f)⁻¹ := eq_inv_of_mul_eq_one_right h
    _ = QuotientGroup.mk' (CFSG.oddCore X) f := inv_eq_of_mul_eq_one_right hfπ2

private theorem map_conj_eq_of_two {U : Type} [Group U]
    (hS : Setup X F) (hQ : CFSG.pCore 2 X ≤ Subgroup.center X)
    {ρ : X →* Multiplicative (ZMod 2) × U}
    (hρker : ρ.ker = EightOne.twoOddCore X) {x : X} (hx2 : (ρ x).2 = 1)
    {f : X} (hf : f ∈ F) (hc2 : orderOf (f * (x * f * x⁻¹)) ∣ 2) :
    QuotientGroup.mk' (CFSG.oddCore X) (x * f * x⁻¹) =
      QuotientGroup.mk' (CFSG.oddCore X) f := by
  have hcK := mul_conj_mem_twoOddCore hS hρker hx2 hf
  have hcQ : f * (x * f * x⁻¹) ∈ CFSG.pCore 2 X :=
    mem_pCore_of_mem_twoOddCore_of_mul_self_eq_one hcK (by
      simpa [pow_two] using
        (orderOf_dvd_iff_pow_eq_one (x := f * (x * f * x⁻¹))).mp hc2)
  have hc1 : f * (x * f * x⁻¹) = 1 := by
    by_contra hne
    have hdx : f * (f * (x * f * x⁻¹)) ∈ F := by
      rw [show f * (f * (x * f * x⁻¹)) = x * f * x⁻¹ by
        rw [← mul_assoc, hS.oddT.mul_self_eq_one hf, one_mul]]
      exact hS.conj_mem x hf
    exact hS.false_of_mul_mem_center hf hdx (hQ hcQ) hne
  have hf'eq : x * f * x⁻¹ = f := by
    have h := congrArg (fun z => f * z) hc1
    rw [mul_one] at h
    rwa [← mul_assoc, hS.oddT.mul_self_eq_one hf, one_mul] at h
  rw [hf'eq]

private theorem ker_snd_le_center {U : Type} [Group U] {W : Subgroup X}
    (hS : Setup X F) (hQ : CFSG.pCore 2 X ≤ Subgroup.center X)
    (hWO : W ≤ CFSG.oddCore X)
    (hWchar : ∀ x ∈ EightOne.twoOddCore X, x ∈ W ↔ Odd (orderOf x))
    (ρ : X →* Multiplicative (ZMod 2) × U)
    (hρker : ρ.ker = EightOne.twoOddCore X)
    (ψ : X ⧸ CFSG.oddCore X →* U)
    (hψπ : ∀ x : X, ψ (QuotientGroup.mk' (CFSG.oddCore X) x) = (ρ x).2) :
    ψ.ker ≤ Subgroup.center (X ⧸ CFSG.oddCore X) := by
  rintro y hy
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore X) y
  have hyE : QuotientGroup.mk' (CFSG.oddCore X) x ∈ ψ.ker := by rw [hx]; exact hy
  rw [← hx]
  have hx2 : (ρ x).2 = 1 := by
    have h := hyE
    rw [MonoidHom.mem_ker] at h
    rwa [hψπ x] at h
  have hcomm : ∀ f ∈ F, QuotientGroup.mk' (CFSG.oddCore X) x *
      QuotientGroup.mk' (CFSG.oddCore X) f =
      QuotientGroup.mk' (CFSG.oddCore X) f *
        QuotientGroup.mk' (CFSG.oddCore X) x := by
    intro f hf
    have hf' : x * f * x⁻¹ ∈ F := hS.conj_mem x hf
    have hff' : QuotientGroup.mk' (CFSG.oddCore X) (x * f * x⁻¹) =
        QuotientGroup.mk' (CFSG.oddCore X) f := by
      rcases hS.oddT.2 f hf (x * f * x⁻¹) hf' with hc2 | hcodd
      · exact map_conj_eq_of_two hS hQ hρker hx2 hf hc2
      · exact map_conj_eq_of_odd hS hWO hWchar hρker hx2 hf hcodd
    have hconj : QuotientGroup.mk' (CFSG.oddCore X) x *
        QuotientGroup.mk' (CFSG.oddCore X) f *
        (QuotientGroup.mk' (CFSG.oddCore X) x)⁻¹ =
        QuotientGroup.mk' (CFSG.oddCore X) f := by
      conv_rhs => rw [← hff']
      rw [map_mul, map_mul, map_inv]
    have h := congrArg (fun z => z * QuotientGroup.mk' (CFSG.oddCore X) x) hconj
    simpa [mul_assoc] using h
  have hgen : Subgroup.closure (QuotientGroup.mk' (CFSG.oddCore X) '' F) = ⊤ := by
    rw [← MonoidHom.map_closure, hS.gen, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective (CFSG.oddCore X))]
  have hle : Subgroup.closure (QuotientGroup.mk' (CFSG.oddCore X) '' F) ≤
      Subgroup.centralizer {QuotientGroup.mk' (CFSG.oddCore X) x} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨f, hf, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm f hf).symm
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.centralizer {QuotientGroup.mk' (CFSG.oddCore X) x} :=
    hle (hgen ▸ Subgroup.mem_top g)
  exact Subgroup.mem_centralizer_singleton_iff.mp hg

private theorem isPGroup_ker_snd {U : Type} [Group U] {W : Subgroup X}
    (hdecomp : ∀ x ∈ EightOne.twoOddCore X, ∃ q ∈ CFSG.pCore 2 X, ∃ o ∈ W, x = q * o)
    (hWO : W ≤ CFSG.oddCore X)
    (ρ : X →* Multiplicative (ZMod 2) × U)
    (hρker : ρ.ker = EightOne.twoOddCore X)
    (ψ : X ⧸ CFSG.oddCore X →* U)
    (hψπ : ∀ x : X, ψ (QuotientGroup.mk' (CFSG.oddCore X) x) = (ρ x).2) :
    IsPGroup 2 ψ.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_orderOf]
  intro y
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore X) (y : X ⧸ CFSG.oddCore X)
  have hyE : QuotientGroup.mk' (CFSG.oddCore X) x ∈ ψ.ker := by rw [hx]; exact y.2
  have hyx : (⟨QuotientGroup.mk' (CFSG.oddCore X) x, hyE⟩ : ψ.ker) = y := Subtype.ext hx
  rw [← hyx]
  have hx2 : (ρ x).2 = 1 := by
    have h := hyE
    rw [MonoidHom.mem_ker] at h
    rwa [hψπ x] at h
  have hρx2 : ρ x * ρ x = 1 := by
    have hz2 : ∀ a : Multiplicative (ZMod 2), a * a = 1 := by
      intro a
      have h := CharTwo.add_self_eq_zero (Multiplicative.toAdd a)
      simpa using congrArg Multiplicative.ofAdd h
    ext
    · exact hz2 (ρ x).1
    · simp [hx2]
  have hx2K : x * x ∈ EightOne.twoOddCore X := by
    rw [← hρker, MonoidHom.mem_ker, map_mul]
    exact hρx2
  obtain ⟨q, hqQ, hπq⟩ := exists_pCore_map_eq hdecomp hWO hx2K
  have hπx2 : (QuotientGroup.mk' (CFSG.oddCore X) x) ^ 2 =
      QuotientGroup.mk' (CFSG.oddCore X) q := by
    rw [pow_two, ← map_mul]; exact hπq
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp
    (CFSG.pCore_isPGroup (p := 2) (G := X))) ⟨q, hqQ⟩
  have hqord : orderOf q = 2 ^ n := by
    simpa using (Subgroup.orderOf_coe (⟨q, hqQ⟩ : CFSG.pCore 2 X)).trans hn
  have hπqpow : (QuotientGroup.mk' (CFSG.oddCore X) q) ^ (2 ^ n) = 1 := by
    refine (orderOf_dvd_iff_pow_eq_one (x := QuotientGroup.mk' (CFSG.oddCore X) q)).mp ?_
    rw [← hqord]
    exact orderOf_map_dvd _ q
  have hpow : (QuotientGroup.mk' (CFSG.oddCore X) x) ^ (2 ^ (n + 1)) = 1 := by
    rw [pow_succ', pow_mul, hπx2, hπqpow]
  have hdvd : orderOf (QuotientGroup.mk' (CFSG.oddCore X) x) ∣ 2 ^ (n + 1) :=
    orderOf_dvd_of_pow_eq_one hpow
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨k, by
    rw [← Subgroup.orderOf_coe (⟨QuotientGroup.mk' (CFSG.oddCore X) x, hyE⟩ : ψ.ker)]
    exact hk⟩

private theorem exists_central_two_kernel {U : Type} [Group U] {W : Subgroup X}
    (hS : Setup X F) (hQ : CFSG.pCore 2 X ≤ Subgroup.center X)
    (hOK : CFSG.oddCore X ≤ EightOne.twoOddCore X)
    (hWO : W ≤ CFSG.oddCore X)
    (hWchar : ∀ x ∈ EightOne.twoOddCore X, x ∈ W ↔ Odd (orderOf x))
    (hdecomp : ∀ x ∈ EightOne.twoOddCore X, ∃ q ∈ CFSG.pCore 2 X, ∃ o ∈ W, x = q * o)
    (φ : X ⧸ EightOne.twoOddCore X ≃* Multiplicative (ZMod 2) × U) :
    ∃ (ρ : X →* Multiplicative (ZMod 2) × U) (ψ : X ⧸ CFSG.oddCore X →* U),
      ρ.ker = EightOne.twoOddCore X ∧
      (∀ x : X, ψ (QuotientGroup.mk' (CFSG.oddCore X) x) = (ρ x).2) ∧
      Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center (X ⧸ CFSG.oddCore X) ∧ IsPGroup 2 ψ.ker := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ : X →* Multiplicative (ZMod 2) × U :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (EightOne.twoOddCore X))
  have hρker : ρ.ker = EightOne.twoOddCore X := by
    rw [show ρ = φ.toMonoidHom.comp (QuotientGroup.mk' (EightOne.twoOddCore X)) from rfl,
      MonoidHom.ker_comp_of_injective _ _ φ.injective, QuotientGroup.ker_mk']
  have hρsurj : Function.Surjective ρ :=
    φ.surjective.comp (QuotientGroup.mk'_surjective (EightOne.twoOddCore X))
  let ψ₀ : X →* U := (MonoidHom.snd _ _).comp ρ
  have hOker : CFSG.oddCore X ≤ ψ₀.ker := by
    intro o ho
    rw [MonoidHom.mem_ker]
    have hoρ : ρ o = 1 := by rw [← MonoidHom.mem_ker, hρker]; exact hOK ho
    show (ρ o).2 = 1
    rw [hoρ]; rfl
  let ψ : X ⧸ CFSG.oddCore X →* U :=
    QuotientGroup.lift (CFSG.oddCore X) ψ₀ hOker
  have hcomp : (QuotientGroup.lift (CFSG.oddCore X) ψ₀ hOker).comp
      (QuotientGroup.mk' (CFSG.oddCore X)) = ψ₀ :=
    QuotientGroup.lift_comp_mk' (CFSG.oddCore X) ψ₀ hOker
  have hψπ : ∀ x : X, ψ (QuotientGroup.mk' (CFSG.oddCore X) x) = (ρ x).2 := by
    intro x
    show (QuotientGroup.lift (CFSG.oddCore X) ψ₀ hOker)
      (QuotientGroup.mk' (CFSG.oddCore X) x) = (ρ x).2
    rw [← MonoidHom.comp_apply, hcomp]
    rfl
  have hψ₀surj : Function.Surjective ψ₀ := by
    intro u
    obtain ⟨x, hx⟩ := hρsurj (1, u)
    exact ⟨x, by simpa [ψ₀] using congrArg Prod.snd hx⟩
  have hψsurj : Function.Surjective ψ := by
    intro u
    obtain ⟨x, hx⟩ := hψ₀surj u
    refine ⟨QuotientGroup.mk' (CFSG.oddCore X) x, ?_⟩
    show (QuotientGroup.lift (CFSG.oddCore X) ψ₀ hOker)
      (QuotientGroup.mk' (CFSG.oddCore X) x) = u
    rw [← MonoidHom.comp_apply, hcomp]
    exact hx
  exact ⟨ρ, ψ, hρker, hψπ, hψsurj,
    ker_snd_le_center hS hQ hWO hWchar ρ hρker ψ hψπ,
    isPGroup_ker_snd hdecomp hWO ρ hρker ψ hψπ⟩

private theorem twoOddCore_le_commutator {U : Type} [Group U]
    (hS : Setup X F)
    (φ : X ⧸ EightOne.twoOddCore X ≃* Multiplicative (ZMod 2) × U) :
    EightOne.twoOddCore X ≤ commutator X := by
  let ρ : X →* Multiplicative (ZMod 2) × U :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (EightOne.twoOddCore X))
  have hρker : ρ.ker = EightOne.twoOddCore X := by
    rw [show ρ = φ.toMonoidHom.comp (QuotientGroup.mk' (EightOne.twoOddCore X)) from rfl,
      MonoidHom.ker_comp_of_injective _ _ φ.injective, QuotientGroup.ker_mk']
  let τ : X →* Multiplicative (ZMod 2) := (MonoidHom.fst _ _).comp ρ
  have hρsurj : Function.Surjective ρ :=
    φ.surjective.comp (QuotientGroup.mk'_surjective (EightOne.twoOddCore X))
  have hτsurj : Function.Surjective τ := by
    intro a
    obtain ⟨x, hx⟩ := hρsurj (a, 1)
    exact ⟨x, by simpa [τ] using congrArg Prod.fst hx⟩
  have hKle : EightOne.twoOddCore X ≤ τ.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    have hkρ : ρ k = 1 := by
      rw [← MonoidHom.mem_ker, hρker]; exact hk
    show (ρ k).1 = 1
    rw [hkρ]; rfl
  have hcommle : commutator X ≤ τ.ker := Abelianization.commutator_subset_ker τ
  have hτindex : τ.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hτsurj, Subgroup.card_top,
      Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hge : τ.ker.index ≤ (commutator X).index := Subgroup.index_antitone hcommle
  have hc2 : (commutator X).index = 2 :=
    le_antisymm hS.index_commutator_le_two (hτindex ▸ hge)
  have hτeq : commutator X = τ.ker := by
    refine Subgroup.eq_of_index_dvd_index hcommle ?_
    rw [hc2, hτindex]
  rw [hτeq]
  exact hKle

private theorem setup_quotient_oddCore (hS : Setup X F) :
    Setup (X ⧸ CFSG.oddCore X) (QuotientGroup.mk' (CFSG.oddCore X) '' F) := by
  refine hS.map (QuotientGroup.mk' (CFSG.oddCore X))
    (QuotientGroup.mk'_surjective (CFSG.oddCore X)) ?_
  intro d hd h1
  exact CFSG.Timmesfeld.Connectivity.not_mem_of_odd_card
    (CFSG.ABGLocalTools.odd_card_oddCore (H := X))
    (hS.oddT.orderOf_eq_two hd) ((QuotientGroup.eq_one_iff d).mp h1)

private theorem ker_inf_commutator_eq_bot {U : Type} [Group U]
    (hS : Setup X F) (hU : CFSG.BenderSuzuki.IsBenderGroup U)
    {ψ : X ⧸ CFSG.oddCore X →* U} (hψsurj : Function.Surjective ψ)
    (hEcent : ψ.ker ≤ Subgroup.center (X ⧸ CFSG.oddCore X))
    (hE2 : IsPGroup 2 ψ.ker) :
    ψ.ker ⊓ commutator (X ⧸ CFSG.oddCore X) = ⊥ := by
  have hSY : Setup (X ⧸ CFSG.oddCore X)
      (QuotientGroup.mk' (CFSG.oddCore X) '' F) := setup_quotient_oddCore hS
  have hB : CFSG.BenderSuzuki.IsBenderGroup ((X ⧸ CFSG.oddCore X) ⧸ ψ.ker) :=
    isBenderGroup_of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj) hU
  have : ψ.ker.Normal := MonoidHom.normal_ker ψ
  exact inf_commutator_eq_bot_of_isBenderGroup hSY hEcent hE2 hB

private theorem pCore_map_eq_bot {U : Type} [Group U]
    (hS : Setup X F)
    (φ : X ⧸ EightOne.twoOddCore X ≃* Multiplicative (ZMod 2) × U)
    {ρ : X →* Multiplicative (ZMod 2) × U}
    (hρker : ρ.ker = EightOne.twoOddCore X)
    {ψ : X ⧸ CFSG.oddCore X →* U}
    (hψπ : ∀ x : X, ψ (QuotientGroup.mk' (CFSG.oddCore X) x) = (ρ x).2)
    (hEinf : ψ.ker ⊓ commutator (X ⧸ CFSG.oddCore X) = ⊥) :
    (CFSG.pCore 2 X).map (QuotientGroup.mk' (CFSG.oddCore X)) = ⊥ := by
  let Q : Subgroup X := CFSG.pCore 2 X
  let K : Subgroup X := EightOne.twoOddCore X
  let π : X →* X ⧸ CFSG.oddCore X := QuotientGroup.mk' (CFSG.oddCore X)
  have hKcomm : K ≤ commutator X := twoOddCore_le_commutator hS φ
  have hQK : Q ≤ K := by
    intro x hx
    show x ∈ (CFSG.oddCore (X ⧸ CFSG.pCore 2 X)).comap
      (QuotientGroup.mk' (CFSG.pCore 2 X))
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  have hQKcomm : Q ≤ commutator X := hQK.trans hKcomm
  have hπQker : Q.map π ≤ ψ.ker := by
    rintro _ ⟨q, hq, rfl⟩
    rw [MonoidHom.mem_ker, hψπ q]
    have hqρ : ρ q = 1 := by
      rw [← MonoidHom.mem_ker, hρker]
      exact hQK hq
    rw [hqρ]; rfl
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hmapcomm : (commutator X).map π = commutator (X ⧸ CFSG.oddCore X) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hπsurj, commutator_def]
  have hπQcomm : Q.map π ≤ commutator (X ⧸ CFSG.oddCore X) := by
    rw [← hmapcomm]
    exact Subgroup.map_mono hQKcomm
  have hπQbot : Q.map π = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hmem : y ∈ ψ.ker ⊓ commutator (X ⧸ CFSG.oddCore X) := ⟨hπQker hy, hπQcomm hy⟩
    rwa [hEinf] at hmem
  exact hπQbot

private theorem pCore_le_oddCore {U : Type} [Group U]
    (hS : Setup X F) (hU : CFSG.BenderSuzuki.IsBenderGroup U)
    (φ : X ⧸ EightOne.twoOddCore X ≃* Multiplicative (ZMod 2) × U)
    (hQ : CFSG.pCore 2 X ≤ Subgroup.center X) :
    CFSG.pCore 2 X ≤ CFSG.oddCore X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Subgroup X := CFSG.pCore 2 X
  let K : Subgroup X := EightOne.twoOddCore X
  let O : Subgroup X := CFSG.oddCore X
  let π : X →* X ⧸ O := QuotientGroup.mk' O
  obtain ⟨W, hWO, hWn, hQinfW, hWchar, hdecomp⟩ :=
    exists_odd_complement_le_oddCore hQ
  have hOK : O ≤ K := oddCore_le_twoOddCore X
  obtain ⟨ρ, ψ, hρker, hψπ, hψsurj, hEcent, hE2⟩ :=
    exists_central_two_kernel hS hQ hOK hWO hWchar hdecomp φ
  have hEinf : ψ.ker ⊓ commutator (X ⧸ O) = ⊥ :=
    ker_inf_commutator_eq_bot hS hU hψsurj hEcent hE2
  have hπQbot : Q.map π = ⊥ := pCore_map_eq_bot hS φ hρker hψπ hEinf
  have hQO : Q ≤ O := by
    have h := (Subgroup.map_eq_bot_iff Q (f := π)).mp hπQbot
    rwa [QuotientGroup.ker_mk'] at h
  exact hQO

private theorem pCore_eq_bot_of_isBenderGroup {U : Type} [Group U]
    (hS : Setup X F) (hU : CFSG.BenderSuzuki.IsBenderGroup U)
    (φ : X ⧸ EightOne.twoOddCore X ≃* Multiplicative (ZMod 2) × U)
    (hQ : CFSG.pCore 2 X ≤ Subgroup.center X) :
    CFSG.pCore 2 X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQO : CFSG.pCore 2 X ≤ CFSG.oddCore X :=
    pCore_le_oddCore hS hU φ hQ
  have hQodd : Odd (Nat.card (CFSG.pCore 2 X)) :=
    (CFSG.ABGLocalTools.odd_card_oddCore (H := X)).of_dvd_nat
      (Subgroup.card_dvd_of_le hQO)
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)).exists_card_eq
  have hcard1 : Nat.card (CFSG.pCore 2 X) = 1 := by
    rw [hn] at hQodd ⊢
    by_contra h
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at h
      exact h rfl
    exact (Nat.not_odd_iff_even.mpr (even_two.pow_of_ne_zero hn0)) hQodd
  exact Subgroup.card_eq_one.mp hcard1

theorem pCore_eq_bot_of_eightOneShape {X : Type} [Group X] [Finite X] {F : Set X}
    (hS : Setup X F) (hX : EightOneShape X) (hQ : CFSG.pCore 2 X ≤ Subgroup.center X) :
    CFSG.pCore 2 X = ⊥ := by
  rcases hX with h | h
  · obtain ⟨φ⟩ := h
    exact pCore_eq_bot_of_isBenderGroup hS (.isPSL2 2 le_rfl (MulEquiv.refl _)) φ hQ
  · obtain ⟨φ⟩ := h
    exact pCore_eq_bot_of_isBenderGroup hS (.isPSU3 2 le_rfl (MulEquiv.refl _)) φ hQ

end CFSG.OddTranspositions.PartThree.ElevenThree
