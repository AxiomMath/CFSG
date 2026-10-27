module

public import CFSG.LocalAnalysis.StandardType.GGFinModelAct
public import CFSG.LocalAnalysis.StandardType.GGFinModelPkg

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.StandardType CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE

section Fixed

@[expose] def ggFixAdd (p : ℕ) {R : ℕ} (π : Equiv.Perm (Fin R)) : AddSubgroup (Fin R → ZMod p) where
  carrier := {z | ∀ i, z (π i) = z i}
  zero_mem' := fun _ => rfl
  add_mem' := fun {a b} ha hb i => by simp [ha i, hb i]
  neg_mem' := fun {a} ha i => by simp [ha i]

theorem mem_ggFixAdd {p R : ℕ} {π : Equiv.Perm (Fin R)} {z : Fin R → ZMod p} :
    z ∈ ggFixAdd p π ↔ ∀ i, z (π i) = z i :=
  Iff.rfl

theorem card_ggFixAdd (p : ℕ) {R : ℕ} (π : Equiv.Perm (Fin R)) :
    Nat.card (ggFixAdd p π) = GGFixCard p π :=
  rfl

@[expose] def ggFixIncl (p : ℕ) {R : ℕ} (π : Equiv.Perm (Fin R)) :
    Multiplicative (ggFixAdd p π) →* Multiplicative (Fin R → ZMod p) :=
  AddMonoidHom.toMultiplicative (ggFixAdd p π).subtype

private theorem ggFixIncl_injective (p : ℕ) {R : ℕ} (π : Equiv.Perm (Fin R)) :
    Function.Injective (ggFixIncl p π) := by
  intro a b h
  apply Multiplicative.toAdd.injective
  exact Subtype.ext (by
    have := congrArg Multiplicative.toAdd h
    simpa [ggFixIncl] using this)

private theorem ggFixAdd_pow_eq_one (p : ℕ) [NeZero p] {R : ℕ} (π : Equiv.Perm (Fin R))
    (z : Multiplicative (ggFixAdd p π)) : z ^ p = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  apply Subtype.ext
  funext i
  simp only [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero, Pi.smul_apply, Pi.zero_apply,
    nsmul_eq_mul, ZMod.natCast_self, zero_mul]

end Fixed

section Param

variable {τ : Tag} {R p : ℕ} [NeZero p]

@[expose] noncomputable def ggParam (hR : R = τ.rank) (ζ : GGLˣ) (z : Fin R → ZMod p) :
    Fin τ.rank → GGLˣ :=
  fun j => ζ ^ ZMod.val (z (Fin.cast hR.symm j))

theorem ggParam_add (hR : R = τ.rank) {ζ : GGLˣ} (hζ : ζ ^ p = 1) (z z' : Fin R → ZMod p) :
    ggParam hR ζ (z + z') = ggParam hR ζ z * ggParam hR ζ z' := by
  funext j
  simp only [ggParam, Pi.add_apply, Pi.mul_apply]
  rw [ZMod.val_add,
    ← pow_eq_pow_mod (m := (z (Fin.cast hR.symm j)).val + (z' (Fin.cast hR.symm j)).val) hζ,
    ← pow_add]

theorem ggParam_zero (hR : R = τ.rank) (ζ : GGLˣ) : ggParam hR ζ (0 : Fin R → ZMod p) = 1 := by
  funext j
  simp [ggParam]

theorem ggParam_eq_one_iff (hR : R = τ.rank) {ζ : GGLˣ} (hζ : orderOf ζ = p) (z : Fin R → ZMod p) :
    ggParam hR ζ z = 1 ↔ z = 0 := by
  constructor
  · intro h
    funext i
    have h2 : p ∣ ZMod.val (z (Fin.cast hR.symm (Fin.cast hR i))) := by
      have hpow : ζ ^ ZMod.val (z (Fin.cast hR.symm (Fin.cast hR i))) = 1 :=
        congrFun h (Fin.cast hR i)
      exact hζ ▸ (orderOf_dvd_iff_pow_eq_one (x := ζ)
        (n := ZMod.val (z (Fin.cast hR.symm (Fin.cast hR i))))).mpr hpow
    have h3 : ZMod.val (z (Fin.cast hR.symm (Fin.cast hR i))) = 0 :=
      Nat.eq_zero_of_dvd_of_lt h2 (ZMod.val_lt _)
    have hcast : Fin.cast hR.symm (Fin.cast hR i) = i := Fin.ext rfl
    rw [hcast] at h3
    exact (ZMod.val_eq_zero (z i)).mp h3
  · intro hz
    rw [hz]
    exact ggParam_zero hR ζ

@[expose] noncomputable def ggDiag (hR : R = τ.rank) {ζ : GGLˣ} (hζ : ζ ^ p = 1) :
    Multiplicative (Fin R → ZMod p) →* ModGL τ GGL :=
  MonoidHom.mk' (fun z => rootDiagUnit τ (ggParam hR ζ (Multiplicative.toAdd z)))
    (fun a b => by rw [toAdd_mul, ggParam_add hR hζ, rootDiagUnit_mul])

end Param

section Data

variable {τ : Tag} {R p : ℕ} [NeZero p] {C : Type} [Group C]

structure GGTorusData (hR : R = τ.rank) (p : ℕ) [NeZero p] (π : Equiv.Perm (Fin R))
    (D : LangDatum τ GGL)
    (ι₀ : C →* ModGL τ GGL) (ζ : GGLˣ) : Prop where
  pkg : GGLangPkg D ι₀
  ζ_order : orderOf ζ = p
  torus_mem : ∀ z : Fin R → ZMod p, (∀ i, z (π i) = z i) →
    rootDiagUnit τ (ggParam hR ζ z) ∈ D.torus

namespace GGTorusData

variable {hR : R = τ.rank} {π : Equiv.Perm (Fin R)} {D : LangDatum τ GGL}
  {ι₀ : C →* ModGL τ GGL} {ζ : GGLˣ} (hT : GGTorusData hR p π D ι₀ ζ)

include hT

theorem ζ_pow : ζ ^ p = 1 := hT.ζ_order ▸ pow_orderOf_eq_one ζ

@[expose] noncomputable def uMap : Multiplicative (ggFixAdd p π) →* ModGL τ GGL :=
  (MulAut.conj D.g0).toMonoidHom.comp ((ggDiag hR hT.ζ_pow).comp (ggFixIncl p π))

theorem uMap_apply (z : Multiplicative (ggFixAdd p π)) :
    hT.uMap z = D.g0 * rootDiagUnit τ (ggParam hR ζ (Multiplicative.toAdd z).1) * D.g0⁻¹ :=
  rfl

theorem uMap_mem_fix (z : Multiplicative (ggFixAdd p π)) : hT.uMap z ∈ D.fix := by
  rw [hT.uMap_apply, ← LangDatum.map_conj_model D]
  refine Subgroup.mem_map.mpr ⟨rootDiagUnit τ (ggParam hR ζ (Multiplicative.toAdd z).1), ?_, ?_⟩
  · exact D.torus_le_model (hT.torus_mem _ (mem_ggFixAdd.mp (Multiplicative.toAdd z).2))
  · exact MulAut.conj_apply D.g0 _

theorem uMap_mem_normalizer (z : Multiplicative (ggFixAdd p π)) :
    hT.uMap z ∈ Subgroup.normalizer (ι₀.range : Set (ModGL τ GGL)) := by
  rw [← hT.pkg.desc.derived]
  exact Subgroup.normalizer_commutator_ge_left D.fix D.fix (hT.uMap_mem_fix z)

@[expose] noncomputable def ggBetaHom : Multiplicative (ggFixAdd p π) →* MulAut C :=
  (ggConjAut ι₀ hT.pkg.inj).comp (MonoidHom.codRestrict hT.uMap _ hT.uMap_mem_normalizer)

theorem ggBetaHom_apply (z : Multiplicative (ggFixAdd p π)) (c : C) :
    ι₀ (hT.ggBetaHom z c) = hT.uMap z * ι₀ c * (hT.uMap z)⁻¹ := by
  rw [ggBetaHom, MonoidHom.comp_apply, MonoidHom.codRestrict_apply]
  exact ggConjAut_apply ι₀ hT.pkg.inj ⟨hT.uMap z, hT.uMap_mem_normalizer z⟩ c

theorem ggBetaHom_injective : Function.Injective hT.ggBetaHom := by
  rw [injective_iff_map_eq_one]
  intro z hz
  have hcomm : ∀ c : C, hT.uMap z * ι₀ c = ι₀ c * hT.uMap z := by
    intro c
    have h1 := ggBetaHom_apply hT z c
    rw [hz] at h1
    simp only [MulAut.one_apply] at h1
    have h2 : ι₀ c * hT.uMap z = hT.uMap z * ι₀ c := by
      conv_lhs => rw [h1]
      group
    exact h2.symm
  have hmem : hT.uMap z ∈ adjointGroup τ GGL :=
    ((LangDatum.mem_fix D).mp (hT.uMap_mem_fix z)).1
  have hone : hT.uMap z = 1 := hT.pkg.cent_triv (hT.uMap z) hmem hcomm
  have ht : rootDiagUnit τ (ggParam hR ζ (Multiplicative.toAdd z).1) = 1 := by
    have h := hT.uMap_apply z
    rw [hone] at h
    have h2 : D.g0 * rootDiagUnit τ (ggParam hR ζ (Multiplicative.toAdd z).1)
        * D.g0⁻¹ = 1 := h.symm
    calc rootDiagUnit τ (ggParam hR ζ (Multiplicative.toAdd z).1)
        = D.g0⁻¹ * (D.g0 * rootDiagUnit τ (ggParam hR ζ (Multiplicative.toAdd z).1)
            * D.g0⁻¹) * D.g0 := by group
      _ = D.g0⁻¹ * 1 * D.g0 := by rw [h2]
      _ = 1 := by group
  have ht' : rootDiagUnit τ (ggParam hR ζ (Multiplicative.toAdd z).1) =
      rootDiagUnit τ (1 : Fin τ.rank → GGLˣ) := by
    rw [ht, rootDiagUnit_one]
  have hp : ggParam hR ζ (Multiplicative.toAdd z).1 = 1 := rootDiagUnit_injective ht'
  have hz0 : (Multiplicative.toAdd z).1 = 0 := (ggParam_eq_one_iff hR hT.ζ_order _).mp hp
  have hz1 : Multiplicative.toAdd z = 0 := Subtype.ext hz0
  have h4 : Multiplicative.toAdd z = Multiplicative.toAdd
      (1 : Multiplicative (ggFixAdd p π)) := by
    rw [hz1, toAdd_one]
  exact Multiplicative.toAdd.injective h4

@[expose] noncomputable def ggBfull : Subgroup (MulAut C) := hT.ggBetaHom.range

@[expose] noncomputable def ggCoord : hT.ggBfull →* Multiplicative (Fin R → ZMod p) :=
  (ggFixIncl p π).comp (MonoidHom.ofInjective hT.ggBetaHom_injective).symm.toMonoidHom

theorem ggCoord_apply (z : Multiplicative (ggFixAdd p π)) :
    hT.ggCoord ⟨hT.ggBetaHom z, ⟨z, rfl⟩⟩ = ggFixIncl p π z := by
  change (ggFixIncl p π) ((MonoidHom.ofInjective hT.ggBetaHom_injective).symm
    (⟨hT.ggBetaHom z, ⟨z, rfl⟩⟩ : ↥hT.ggBetaHom.range)) = ggFixIncl p π z
  apply congrArg (ggFixIncl p π)
  apply hT.ggBetaHom_injective
  rw [MonoidHom.apply_ofInjective_symm]

theorem ggCoord_injective : Function.Injective hT.ggCoord := by
  have h1 : Function.Injective (ggFixIncl p π) := ggFixIncl_injective p π
  have h2 : Function.Injective
      (MonoidHom.ofInjective hT.ggBetaHom_injective).symm.toMonoidHom :=
    (MonoidHom.ofInjective hT.ggBetaHom_injective).symm.injective
  show Function.Injective (fun b : ↥hT.ggBfull => (ggFixIncl p π)
    ((MonoidHom.ofInjective hT.ggBetaHom_injective).symm.toMonoidHom b))
  exact h1.comp h2

theorem ggCoord_fixed (b : hT.ggBfull) (i : Fin R) :
    Multiplicative.toAdd (hT.ggCoord b) (π i) = Multiplicative.toAdd (hT.ggCoord b) i := by
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp b.2
  have hb : b = ⟨hT.ggBetaHom z, ⟨z, rfl⟩⟩ := Subtype.ext hz.symm
  rw [hb, hT.ggCoord_apply z]
  simpa [ggFixIncl] using mem_ggFixAdd.mp (Multiplicative.toAdd z).2 i

theorem ggBfull_isElemAbelian : IsElemAbelian p hT.ggBfull := by
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · intro a b
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp a.2
    obtain ⟨z', hz'⟩ := MonoidHom.mem_range.mp b.2
    apply Subtype.ext
    show (a : MulAut C) * (b : MulAut C) = (b : MulAut C) * (a : MulAut C)
    rw [← hz, ← hz']
    rw [← map_mul, ← map_mul, mul_comm z z']
  · intro x hx
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp hx
    rw [← hz, ← map_pow, ggFixAdd_pow_eq_one p π z, map_one]

theorem ggBfull_card : Nat.card hT.ggBfull = GGFixCard p π := by
  rw [← card_ggFixAdd p π]
  calc Nat.card hT.ggBfull
      = Nat.card (Multiplicative (ggFixAdd p π)) :=
        Nat.card_congr (MonoidHom.ofInjective hT.ggBetaHom_injective).toEquiv.symm
    _ = Nat.card (ggFixAdd p π) := Nat.card_congr Multiplicative.toAdd

theorem ggBetaHom_mem_inn_iff (z : Multiplicative (ggFixAdd p π)) :
    hT.ggBetaHom z ∈ (MulAut.conj : C →* MulAut C).range ↔ hT.uMap z ∈ ι₀.range := by
  constructor
  · rintro ⟨c, hc⟩
    have hcomm : ∀ x : C,
        ((ι₀ c)⁻¹ * hT.uMap z) * ι₀ x = ι₀ x * ((ι₀ c)⁻¹ * hT.uMap z) := by
      intro x
      have h := ggBetaHom_apply hT z x
      rw [← hc] at h
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv] at h
      calc (ι₀ c)⁻¹ * hT.uMap z * ι₀ x
          = (ι₀ c)⁻¹ * (hT.uMap z * ι₀ x * (hT.uMap z)⁻¹) * hT.uMap z := by group
        _ = (ι₀ c)⁻¹ * (ι₀ c * ι₀ x * (ι₀ c)⁻¹) * hT.uMap z := by rw [← h]
        _ = ι₀ x * ((ι₀ c)⁻¹ * hT.uMap z) := by group
    have hmem : (ι₀ c)⁻¹ * hT.uMap z ∈ adjointGroup τ GGL := by
      have hfix : (ι₀ c)⁻¹ * hT.uMap z ∈ D.fix :=
        D.fix.mul_mem (D.fix.inv_mem (hT.pkg.desc.range_le ⟨c, rfl⟩)) (hT.uMap_mem_fix z)
      exact ((LangDatum.mem_fix D).mp hfix).1
    have hone : (ι₀ c)⁻¹ * hT.uMap z = 1 := hT.pkg.cent_triv _ hmem hcomm
    exact MonoidHom.mem_range.mpr ⟨c, inv_mul_eq_one.mp hone⟩
  · rintro ⟨c, hc⟩
    refine MonoidHom.mem_range.mpr ⟨c, ?_⟩
    ext x
    apply hT.pkg.inj
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hc, ggBetaHom_apply]

theorem ggBfull_index_inner (hp3 : 3 ≤ p) :
    Nat.card hT.ggBfull ≤
      p * Nat.card ↥(hT.ggBfull ⊓ (MulAut.conj : C →* MulAut C).range) := by
  let H : Subgroup ↥D.fix := ι₀.range.subgroupOf D.fix
  haveI hHnorm : H.Normal := Subgroup.normal_subgroupOf_of_le_normalizer (by
    rw [← hT.pkg.desc.derived]
    exact Subgroup.normalizer_commutator_ge_left D.fix D.fix)
  let uFix : Multiplicative (ggFixAdd p π) →* ↥D.fix :=
    MonoidHom.codRestrict hT.uMap D.fix hT.uMap_mem_fix
  let θ : Multiplicative (ggFixAdd p π) →* (↥D.fix ⧸ H) := (QuotientGroup.mk' H).comp uFix
  let e : Multiplicative (ggFixAdd p π) ≃* ↥hT.ggBfull :=
    MonoidHom.ofInjective hT.ggBetaHom_injective
  let θbar : ↥hT.ggBfull →* (↥D.fix ⧸ H) := θ.comp e.symm.toMonoidHom
  have hθker : ∀ z : Multiplicative (ggFixAdd p π), θ z = 1 ↔ hT.uMap z ∈ ι₀.range := by
    intro z
    change (QuotientGroup.mk' H) (uFix z) = 1 ↔ hT.uMap z ∈ ι₀.range
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff (uFix z),
      Subgroup.mem_subgroupOf]
    rfl
  have hker : θbar.ker =
      (hT.ggBfull ⊓ (MulAut.conj : C →* MulAut C).range).subgroupOf hT.ggBfull := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    change θ (e.symm b) = 1 ↔ (b : MulAut C) ∈ hT.ggBfull ∧
      (b : MulAut C) ∈ (MulAut.conj : C →* MulAut C).range
    have hb : (b : MulAut C) = hT.ggBetaHom (e.symm b) := by
      rw [← MonoidHom.ofInjective_apply hT.ggBetaHom_injective (x := e.symm b)]
      exact (congrArg Subtype.val (e.apply_symm_apply b)).symm
    rw [hθker, hb]
    constructor
    · intro hu
      exact ⟨MonoidHom.mem_range.mpr ⟨e.symm b, rfl⟩,
        (hT.ggBetaHom_mem_inn_iff (e.symm b)).mpr hu⟩
    · rintro ⟨_, hinn⟩
      exact (hT.ggBetaHom_mem_inn_iff (e.symm b)).mp hinn
  haveI hfin : Finite (↥D.fix ⧸ H) := by
    haveI := hT.pkg.desc.finite_fix
    exact Quotient.finite (QuotientGroup.leftRel H)
  have hcard_range : Nat.card θbar.range ≤ p := by
    have h1 : Nat.card θbar.range ≤ Nat.card (↥D.fix ⧸ H) :=
      Subgroup.card_le_card_group θbar.range
    have h2 : Nat.card (↥D.fix ⧸ H) ≤ 3 := by
      change H.index ≤ 3
      exact hT.pkg.index_le
    exact le_trans h1 (le_trans h2 hp3)
  have hcard_ker : Nat.card θbar.ker =
      Nat.card ↥(hT.ggBfull ⊓ (MulAut.conj : C →* MulAut C).range) := by
    rw [hker,
      ← Subgroup.card_subtype hT.ggBfull
        ((hT.ggBfull ⊓ (MulAut.conj : C →* MulAut C).range).subgroupOf hT.ggBfull),
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left]
  calc Nat.card hT.ggBfull
      = Nat.card (↥hT.ggBfull ⧸ θbar.ker) * Nat.card θbar.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup θbar.ker
    _ = Nat.card θbar.range * Nat.card θbar.ker := by
        rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange θbar).toEquiv]
    _ = Nat.card θbar.range *
        Nat.card ↥(hT.ggBfull ⊓ (MulAut.conj : C →* MulAut C).range) := by rw [hcard_ker]
    _ ≤ p * Nat.card ↥(hT.ggBfull ⊓ (MulAut.conj : C →* MulAut C).range) :=
        Nat.mul_le_mul_right _ hcard_range

theorem ggBfull_le_inn (hco : Nat.Coprime p (ι₀.range.relIndex D.fix)) :
    hT.ggBfull ≤ (MulAut.conj : C →* MulAut C).range := by
  intro b hb
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp hb
  rw [← hz, hT.ggBetaHom_mem_inn_iff]
  let H : Subgroup ↥D.fix := ι₀.range.subgroupOf D.fix
  haveI hHnorm : H.Normal := Subgroup.normal_subgroupOf_of_le_normalizer (by
    rw [← hT.pkg.desc.derived]
    exact Subgroup.normalizer_commutator_ge_left D.fix D.fix)
  let uFix : Multiplicative (ggFixAdd p π) →* ↥D.fix :=
    MonoidHom.codRestrict hT.uMap D.fix hT.uMap_mem_fix
  let x : ↥D.fix ⧸ H := QuotientGroup.mk' H (uFix z)
  have hxp : x ^ p = 1 := by
    change (QuotientGroup.mk' H (uFix z)) ^ p = 1
    rw [← map_pow, ← map_pow, ggFixAdd_pow_eq_one p π z, map_one, map_one]
  have hxr : x ^ (ι₀.range.relIndex D.fix) = 1 := by
    change x ^ H.index = 1
    exact pow_card_eq_one'
  have hx1 : x = 1 := by
    have h1 : orderOf x ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hxp
    have h2 : orderOf x ∣ ι₀.range.relIndex D.fix := orderOf_dvd_iff_pow_eq_one.mpr hxr
    have h3 : orderOf x ∣ Nat.gcd p (ι₀.range.relIndex D.fix) := Nat.dvd_gcd h1 h2
    rw [hco.gcd_eq_one] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have hmem : (uFix z : ↥D.fix) ∈ H :=
    (QuotientGroup.eq_one_iff (uFix z)).mp (by
      change (QuotientGroup.mk' H (uFix z)) = 1
      exact hx1)
  show hT.uMap z ∈ ι₀.range
  exact Subgroup.mem_subgroupOf.mp hmem

end GGTorusData

end Data

end CFSG.StandardType.GGFinModel
