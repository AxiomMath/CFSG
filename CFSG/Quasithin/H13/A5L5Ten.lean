module

public import CFSG.Quasithin.H13.A5LNat
public import CFSG.Quasithin.Background.G64ExtSq

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open Matrix Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Wedge

@[expose] def e5 (i : Fin 5) : Fin 5 → ZMod 2 := Pi.single i 1

@[expose] noncomputable def t5Lin : (Fin 5 → ZMod 2) →ₗ[ZMod 2] (Fin 5 → ZMod 2) :=
  Matrix.toLin' t5

theorem t5Lin_apply (u : Fin 5 → ZMod 2) : t5Lin u = t5 *ᵥ u := Matrix.toLin'_apply t5 u

@[expose] noncomputable def w5 (i : Fin 5) : ⋀[ZMod 2]^2 (Fin 5 → ZMod 2) :=
  exteriorPower.ιMulti (ZMod 2) 2 ![e5 i, e5 4]

@[expose] noncomputable def commT5 :
    ⋀[ZMod 2]^2 (Fin 5 → ZMod 2) →ₗ[ZMod 2] ⋀[ZMod 2]^2 (Fin 5 → ZMod 2) :=
  exteriorPower.map 2 t5Lin - LinearMap.id

@[expose] noncomputable def phi5 (j : Fin 5) : ⋀[ZMod 2]^2 (Fin 5 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  G64.wedgeForm (LinearMap.proj j) (LinearMap.proj 0)

theorem t5_vals : ∀ i j : Fin 5, (t5 *ᵥ e5 i) j = if i = 4 ∧ j = 0 then 1 else e5 i j := by
  decide +kernel

theorem phi5_commT5 (i j : Fin 5) (hi : i ≠ 0 ∧ i ≠ 4) (hj : j ≠ 0 ∧ j ≠ 4) :
    phi5 j (commT5 (w5 i)) = if i = j then 1 else 0 := by
  have h := G64.wedgeForm_comm t5Lin (LinearMap.proj j) (LinearMap.proj 0) (e5 i) (e5 4)
  simp only [commT5, LinearMap.sub_apply, LinearMap.id_apply, phi5, w5]
  rw [h]
  simp only [LinearMap.proj_apply, t5Lin_apply, t5_vals]
  clear h
  revert i j
  decide +kernel

@[expose] noncomputable def m5 (a : Fin 3 → ZMod 2) : ⋀[ZMod 2]^2 (Fin 5 → ZMod 2) :=
  a 0 • w5 1 + a 1 • w5 2 + a 2 • w5 3

theorem phi5_commT5_m5 (a : Fin 3 → ZMod 2) :
    phi5 1 (commT5 (m5 a)) = a 0 ∧ phi5 2 (commT5 (m5 a)) = a 1 ∧
      phi5 3 (commT5 (m5 a)) = a 2 := by
  simp only [m5, map_add, map_smul, smul_eq_mul]
  rw [phi5_commT5 1 1 (by decide) (by decide), phi5_commT5 2 1 (by decide) (by decide),
    phi5_commT5 3 1 (by decide) (by decide), phi5_commT5 1 2 (by decide) (by decide),
    phi5_commT5 2 2 (by decide) (by decide), phi5_commT5 3 2 (by decide) (by decide),
    phi5_commT5 1 3 (by decide) (by decide), phi5_commT5 2 3 (by decide) (by decide),
    phi5_commT5 3 3 (by decide) (by decide)]
  refine ⟨?_, ?_, ?_⟩ <;> simp

theorem commT5_m5_injective {a b : Fin 3 → ZMod 2}
    (h : exteriorPower.map 2 t5Lin (m5 a) - m5 a = exteriorPower.map 2 t5Lin (m5 b) - m5 b) :
    a = b := by
  have h' : commT5 (m5 a) = commT5 (m5 b) := by
    simp only [commT5, LinearMap.sub_apply, LinearMap.id_apply]
    exact h
  obtain ⟨ha1, ha2, ha3⟩ := phi5_commT5_m5 a
  obtain ⟨hb1, hb2, hb3⟩ := phi5_commT5_m5 b
  have e0 : a 0 = b 0 := by rw [← ha1, ← hb1, h']
  have e1 : a 1 = b 1 := by rw [← ha2, ← hb2, h']
  have e2 : a 2 = b 2 := by rw [← ha3, ← hb3, h']
  funext j
  fin_cases j
  · exact e0
  · exact e1
  · exact e2

end Wedge

section Fact

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def commHom (v : MulAut V) : V →* V where
  toFun w := v w * w⁻¹
  map_one' := by rw [map_one, inv_one, mul_one]
  map_mul' a b := by
    rw [map_mul, _root_.mul_inv_rev]
    simp only [mul_comm, mul_left_comm, mul_assoc]

omit [Finite V] in
theorem ker_commHom (v : MulAut V) : (commHom v).ker = fixV (Subgroup.zpowers v) := by
  ext w
  rw [MonoidHom.mem_ker, mem_fixV_zpowers_iff]
  show v w * w⁻¹ = 1 ↔ v w = w
  exact mul_inv_eq_one

theorem factL5TenRow1321 : FactL5TenRow1321 := by
  intro V _ _ hV G L A v hB4 hc h11
  obtain ⟨hGJ, hJL, hcardV, -, π, hπ, -⟩ := h11
  have hGL : G = L := hGJ.trans hJL
  have hvL : v ∈ L := hGL ▸ hc.mem
  have hinj : Function.Injective π :=
    G64.RealizesVia.injective_of_faithful' (G64.extSq_faithful (by norm_num)) hπ
  let eπ : ↥(StatedSL 5 (ZMod 2)) ≃* ↥L := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  obtain ⟨E₀, hE₀⟩ := G64.RealizesVia.exists_secEquiv (D := FFModel.extSq (ZMod 2) 5) rfl hπ
  let E : V ≃* Multiplicative (⋀[ZMod 2]^2 (Fin 5 → ZMod 2)) := E₀.trans Subgroup.topEquiv
  have hE : ∀ (γ : ↥(StatedSL 5 (ZMod 2))) (w : V),
      E (((π γ : ↥L) : MulAut V) w) = extSqAct (ZMod 2) 5 γ (E w) := fun γ w => hE₀ γ w
  have htop : StatedSL 5 (ZMod 2) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    refine Subgroup.subset_closure ?_
    show ((g : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)).det = 1
    have h1 : Matrix.GeneralLinearGroup.det g = 1 := Subsingleton.elim _ _
    have h2 := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1
    simpa using h2
  let ψ₀ : ↥(StatedSL 5 (ZMod 2)) ≃* GL (Fin 5) (ZMod 2) :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  have hψ₀ : ∀ γ : ↥(StatedSL 5 (ZMod 2)), ψ₀ γ = (γ : GL (Fin 5) (ZMod 2)) := fun _ => rfl
  let ψ : ↥L ≃* GL (Fin 5) (ZMod 2) := eπ.symm.trans ψ₀
  obtain ⟨S, hS, hSv⟩ := hc.sylow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSp : IsPGroup 2 (S.subgroupOf L) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  have hPp : IsPGroup 2 ((S.subgroupOf L).map (ψ : ↥L →* GL (Fin 5) (ZMod 2))) := hSp.map _
  have hPi : ¬ 2 ∣ ((S.subgroupOf L).map (ψ : ↥L →* GL (Fin 5) (ZMod 2))).index := by
    rw [Subgroup.index_map_equiv]
    exact hS.2.2
  let P : Sylow 2 (GL (Fin 5) (ZMod 2)) := hPp.toSylow hPi
  set M := ψ ⟨v, hvL⟩ with hM
  have hM2 : M * M = 1 := by
    rw [hM, ← map_mul]
    have : (⟨v, hvL⟩ : ↥L) * ⟨v, hvL⟩ = 1 := Subtype.ext hc.sq
    rw [this, map_one]
  have hM1 : M ≠ 1 := by
    intro h
    apply hc.ne_one
    rw [hM, MulEquiv.map_eq_one_iff] at h
    exact congrArg Subtype.val h
  have hcomm : ∀ g ∈ P, M * g = g * M := by
    intro g hg
    rw [IsPGroup.mem_toSylow] at hg
    obtain ⟨⟨s, hsL⟩, hs, rfl⟩ := hg
    have hsS : s ∈ S := Subgroup.mem_subgroupOf.mp hs
    have hsv : s * v = v * s := Subgroup.mem_centralizer_singleton_iff.mp (hSv hsS)
    show ψ ⟨v, hvL⟩ * ψ ⟨s, hsL⟩ = ψ ⟨s, hsL⟩ * ψ ⟨v, hvL⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hsv.symm
  obtain ⟨g, hg⟩ := exists_conj_of_comm_sylow uniGL5_isPGroup uniGL5_index uniGL5_center P
    hM2 hM1 hcomm
  let T : GL (Fin 5) (ZMod 2) := uniUnit (isUni_mk5 (Pi.single 3 1))
  have hT : g⁻¹ * M * g = T := Units.ext hg
  obtain ⟨γ₀, hγ₀⟩ : ∃ γ₀ : ↥(StatedSL 5 (ZMod 2)), (γ₀ : GL (Fin 5) (ZMod 2)) = T :=
    ⟨ψ₀.symm T, ψ₀.apply_symm_apply T⟩
  obtain ⟨h, hh⟩ : ∃ h : ↥L, ψ h = g := ⟨ψ.symm g, ψ.apply_symm_apply g⟩
  have hv : (⟨v, hvL⟩ : ↥L) = h * π γ₀ * h⁻¹ := by
    apply ψ.injective
    rw [map_mul, map_mul, map_inv, hh]
    have h1 : ψ (π γ₀) = T := by
      show ψ₀ (eπ.symm (eπ γ₀)) = T
      rw [MulEquiv.symm_apply_apply, hψ₀, hγ₀]
    rw [h1, ← hT, ← hM]
    group
  have hvV : v = (h : MulAut V) * ((π γ₀ : ↥L) : MulAut V) * (h : MulAut V)⁻¹ :=
    congrArg Subtype.val hv
  let Φ : V → ⋀[ZMod 2]^2 (Fin 5 → ZMod 2) := fun w => Multiplicative.toAdd (E w)
  have hΦmul : ∀ a b : V, Φ (a * b⁻¹) = Φ a - Φ b := by
    intro a b
    show Multiplicative.toAdd (E (a * b⁻¹)) = _
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, sub_eq_add_neg]
  have hx : (G64.glLin 5 (γ₀ : GL (Fin 5) (ZMod 2))).toLinearMap = t5Lin := by
    apply LinearMap.ext
    intro u
    show G64.glLin 5 (γ₀ : GL (Fin 5) (ZMod 2)) u = t5Lin u
    rw [G64.glLin_apply, hγ₀, t5Lin_apply]
    rfl
  have hΦact : ∀ w : V, Φ (((π γ₀ : ↥L) : MulAut V) w) = exteriorPower.map 2 t5Lin (Φ w) := by
    intro w
    show Multiplicative.toAdd (E (((π γ₀ : ↥L) : MulAut V) w)) = _
    rw [hE, G64.extSqAct_apply, hx]
  have hΦE : ∀ m : ⋀[ZMod 2]^2 (Fin 5 → ZMod 2), Φ (E.symm (Multiplicative.ofAdd m)) = m := by
    intro m
    show Multiplicative.toAdd (E (E.symm (Multiplicative.ofAdd m))) = m
    rw [MulEquiv.apply_symm_apply]
    rfl
  let wa : (Fin 3 → ZMod 2) → V := fun a =>
    (h : MulAut V) (E.symm (Multiplicative.ofAdd (m5 a)))
  have hcv : ∀ a, commHom v (wa a) = (h : MulAut V)
      (commHom ((π γ₀ : ↥L) : MulAut V) (E.symm (Multiplicative.ofAdd (m5 a)))) := by
    intro a
    show v (wa a) * (wa a)⁻¹ = _
    rw [hvV]
    show (h : MulAut V) (((π γ₀ : ↥L) : MulAut V) ((h : MulAut V)⁻¹ ((h : MulAut V)
      (E.symm (Multiplicative.ofAdd (m5 a)))))) * (wa a)⁻¹ = _
    rw [MulAut.inv_apply_self]
    show _ = (h : MulAut V) (((π γ₀ : ↥L) : MulAut V) (E.symm (Multiplicative.ofAdd (m5 a))) *
        (E.symm (Multiplicative.ofAdd (m5 a)))⁻¹)
    rw [map_mul, map_inv]
  have hinj8 : Function.Injective fun a => commHom v (wa a) := by
    intro a b hab
    simp only [hcv] at hab
    have h1 := (h : MulAut V).injective hab
    have h2 := congrArg Φ h1
    simp only [commHom, MonoidHom.coe_mk, OneHom.coe_mk, hΦmul, hΦact, hΦE] at h2
    exact commT5_m5_injective h2
  have hidx : 8 ≤ (fixV (Subgroup.zpowers v)).index := by
    rw [← ker_commHom, Subgroup.index_ker]
    have h1 := Nat.card_le_card_of_injective
      (fun a => (⟨commHom v (wa a), MonoidHom.mem_range.mpr ⟨wa a, rfl⟩⟩ :
        ↥(commHom v).range))
      (fun a b hab => hinj8 (congrArg Subtype.val hab))
    rw [Nat.card_eq_fintype_card (α := Fin 3 → ZMod 2), Fintype.card_fun, ZMod.card,
      Fintype.card_fin] at h1
    exact (by norm_num : (8 : ℕ) ≤ 2 ^ 3).trans h1
  have hdvd : (fixV (Subgroup.zpowers v)).index ∣ 2 ^ 10 :=
    hcardV ▸ Subgroup.index_dvd_card _
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hrk := hc.rank
  unfold rkIdx at hrk
  rw [hk, padicValNat.prime_pow] at hrk
  rw [hk] at hidx
  interval_cases k <;> norm_num at hidx

end Fact

end CFSG.Quasithin.H13.A5
