module

public import CFSG.Quasithin.MS93.S46KC2
public import CFSG.Quasithin.MS93.S46KCFLin
public import CFSG.Quasithin.MS93.S46KC2Grp

public section

namespace CFSG.Quasithin.MS93.S46.KCF

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46 CFSG.Quasithin.MS93.S46.X3
  CFSG.Quasithin.MS93.S46.KC2
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)} {c : Hyp46 M T L φ} {α β γ : Vtx (puAmalgam c.pu.le)}
  {ψ : ↥(stab (puAmalgam c.pu.le) α) →* ↥(StatedSL 3 F)}

theorem commute_of_mem_zm (d : X3Data c α β γ ψ) {a g : (puAmalgam c.pu.le).Universal}
    (ha : a ∈ ZM (puAmalgam c.pu.le) α) (hg : g ∈ Qv (puAmalgam c.pu.le) α) : Commute a g :=
  (Subgroup.mem_centralizer_iff.mp (d.lh.zq ha) g hg).symm

theorem natVecG_commutator_mul_right (d : X3Data c α β γ ψ)
    (hVU : ⁅Vv (puAmalgam c.pu.le) α, Vv (puAmalgam c.pu.le) α⁆ ≤ Uloc c.pu.le L α)
    {z v v' : (puAmalgam c.pu.le).Universal} (hz : z ∈ Vv (puAmalgam c.pu.le) α)
    (hv : v ∈ Vv (puAmalgam c.pu.le) α) (hv' : v' ∈ Vv (puAmalgam c.pu.le) α) :
    natVecG d.lh.nat ⁅z, v * v'⁆ = natVecG d.lh.nat ⁅z, v⁆ + natVecG d.lh.nat ⁅z, v'⁆ := by
  have h1 : ⁅z, v⁆ ∈ Uloc c.pu.le L α := hVU (Subgroup.commutator_mem_commutator hz hv)
  have h2 : ⁅z, v'⁆ ∈ Uloc c.pu.le L α := hVU (Subgroup.commutator_mem_commutator hz hv')
  have hc : Commute ⁅z, v'⁆ v := commute_of_mem_zm d (d.lh.uZ h2) (d.lh.vq hv)
  have e : ⁅z, v * v'⁆ = ⁅z, v⁆ * ⁅z, v'⁆ := by
    calc ⁅z, v * v'⁆ = ⁅z, v⁆ * (v * ⁅z, v'⁆ * v⁻¹) := by
          simp only [commutatorElement_def]
          group
      _ = ⁅z, v⁆ * ⁅z, v'⁆ := by rw [hc.symm.eq, mul_inv_cancel_right]
  rw [e, natVecG_mul d.lh.nat h1 h2]

theorem natVecG_commutator_mul_left (d : X3Data c α β γ ψ)
    (hVU : ⁅Vv (puAmalgam c.pu.le) α, Vv (puAmalgam c.pu.le) α⁆ ≤ Uloc c.pu.le L α)
    {z z' v : (puAmalgam c.pu.le).Universal} (hz : z ∈ Vv (puAmalgam c.pu.le) α)
    (hz' : z' ∈ Vv (puAmalgam c.pu.le) α) (hv : v ∈ Vv (puAmalgam c.pu.le) α) :
    natVecG d.lh.nat ⁅z * z', v⁆ = natVecG d.lh.nat ⁅z, v⁆ + natVecG d.lh.nat ⁅z', v⁆ := by
  have h1 : ⁅z, v⁆ ∈ Uloc c.pu.le L α := hVU (Subgroup.commutator_mem_commutator hz hv)
  have h2 : ⁅z', v⁆ ∈ Uloc c.pu.le L α := hVU (Subgroup.commutator_mem_commutator hz' hv)
  rw [commutator_mul_of_commute (commute_of_mem_zm d (d.lh.uZ h2) (d.lh.vq hz)),
    natVecG_mul d.lh.nat h2 h1, add_comm]

theorem natVecG_commutator_inv_mul (d : X3Data c α β γ ψ)
    (hVU : ⁅Vv (puAmalgam c.pu.le) α, Vv (puAmalgam c.pu.le) α⁆ ≤ Uloc c.pu.le L α)
    {z v w : (puAmalgam c.pu.le).Universal} (hz : z ∈ Vv (puAmalgam c.pu.le) α)
    (hv : v ∈ Vv (puAmalgam c.pu.le) α) (hw : w ∈ Vv (puAmalgam c.pu.le) α) :
    natVecG d.lh.nat ⁅z, v⁻¹ * w⁆ = natVecG d.lh.nat ⁅z, w⁆ - natVecG d.lh.nat ⁅z, v⁆ := by
  have h := natVecG_commutator_mul_right d hVU hz hv (Subgroup.mul_mem _ (Subgroup.inv_mem _ hv) hw)
  rw [mul_inv_cancel_left] at h
  rw [h]
  abel

theorem natVecG_commutator_comm [CharP F 2] (d : X3Data c α β γ ψ)
    (hVU : ⁅Vv (puAmalgam c.pu.le) α, Vv (puAmalgam c.pu.le) α⁆ ≤ Uloc c.pu.le L α)
    {a b : (puAmalgam c.pu.le).Universal} (ha : a ∈ Vv (puAmalgam c.pu.le) α)
    (hb : b ∈ Vv (puAmalgam c.pu.le) α) :
    natVecG d.lh.nat ⁅a, b⁆ = natVecG d.lh.nat ⁅b, a⁆ := by
  have h1 : ⁅a, b⁆ ∈ Uloc c.pu.le L α := hVU (Subgroup.commutator_mem_commutator ha hb)
  have h := natVecG_mul d.lh.nat (Subgroup.inv_mem _ h1) h1
  rw [inv_mul_cancel, natVecG_one, commutatorElement_inv] at h
  have e : natVecG d.lh.nat ⁅b, a⁆ = -natVecG d.lh.nat ⁅a, b⁆ := eq_neg_of_add_eq_zero_left h.symm
  rw [e]
  funext k
  exact (CharTwo.neg_eq _).symm

theorem natVecG_commutator_conj (d : X3Data c α β γ ψ)
    (h2 : ∀ k : ↥(stab (puAmalgam c.pu.le) α), toSL3 ψ k ∈ (rootGroup 2 1 : Subgroup (SL3 F)) →
      ∀ z ∈ ZM (puAmalgam c.pu.le) γ, ⁅z, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ ZM _ α)
    (hVU : ⁅Vv (puAmalgam c.pu.le) α, Vv (puAmalgam c.pu.le) α⁆ ≤ Uloc c.pu.le L α)
    {z v : (puAmalgam c.pu.le).Universal} (hz : z ∈ ZM (puAmalgam c.pu.le) γ)
    (hv : v ∈ Vv (puAmalgam c.pu.le) α) {k : ↥(stab (puAmalgam c.pu.le) α)}
    (hk : (toSL3 ψ k : Matrix (Fin 3) (Fin 3) F) 0 = Pi.single 0 1) :
    natVecG d.lh.nat ⁅z, (k : (puAmalgam c.pu.le).Universal) * v *
        (k : (puAmalgam c.pu.le).Universal)⁻¹⁆ =
      (toSL3 ψ k : Matrix (Fin 3) (Fin 3) F) *ᵥ natVecG d.lh.nat ⁅z, v⁆ := by
  have hzV : z ∈ Vv (puAmalgam c.pu.le) α := d.zγVα hz
  have hk' : (toSL3 ψ k⁻¹ : Matrix (Fin 3) (Fin 3) F) 0 = Pi.single 0 1 := by
    have h := row_mul_inv (A := (1 : SL3 F)) (B := toSL3 ψ k) (by rw [row_one, hk])
    rwa [one_mul, ← map_inv] at h
  have hc : ⁅z⁻¹, ((k⁻¹ : ↥(stab (puAmalgam c.pu.le) α)) : (puAmalgam c.pu.le).Universal)⁆ ∈
      ZM (puAmalgam c.pu.le) α := commutator_mem_of_row d h2 (Subgroup.inv_mem _ hz) hk'
  rw [Subgroup.coe_inv] at hc
  have e1 : (k : (puAmalgam c.pu.le).Universal)⁻¹ * z * k =
      z * ⁅z⁻¹, (k : (puAmalgam c.pu.le).Universal)⁻¹⁆ := by
    simp only [commutatorElement_def]
    group
  have e2 : ⁅z, (k : (puAmalgam c.pu.le).Universal) * v * (k : (puAmalgam c.pu.le).Universal)⁻¹⁆ =
      (k : (puAmalgam c.pu.le).Universal) * ⁅(k : (puAmalgam c.pu.le).Universal)⁻¹ * z * k, v⁆ *
        (k : (puAmalgam c.pu.le).Universal)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e2, e1, commutator_mul_left_eq (commute_of_mem_zm d hc (d.lh.vq hv))]
  exact natVecG_conj d.lh.nat k (hVU (Subgroup.commutator_mem_commutator hzV hv))

theorem natVecG_commutator_conj_left (d : X3Data c α β γ ψ)
    (hVU : ⁅Vv (puAmalgam c.pu.le) α, Vv (puAmalgam c.pu.le) α⁆ ≤ Uloc c.pu.le L α)
    {w v : (puAmalgam c.pu.le).Universal} (hw : w ∈ Vv (puAmalgam c.pu.le) α)
    (hv : v ∈ Vv (puAmalgam c.pu.le) α) (g : ↥(stab (puAmalgam c.pu.le) α)) :
    natVecG d.lh.nat ⁅(g : (puAmalgam c.pu.le).Universal)⁻¹ * w * g, v⁆ =
      (((toSL3 ψ g)⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        natVecG d.lh.nat ⁅w, (g : (puAmalgam c.pu.le).Universal) * v *
          (g : (puAmalgam c.pu.le).Universal)⁻¹⁆ := by
  have hgv : (g : (puAmalgam c.pu.le).Universal) * v * (g : (puAmalgam c.pu.le).Universal)⁻¹ ∈
      Vv (puAmalgam c.pu.le) α := (Subgroup.mem_normalizer_iff.mp (d.lh.vN g.2) v).mp hv
  have e : ⁅(g : (puAmalgam c.pu.le).Universal)⁻¹ * w * g, v⁆ =
      ((g⁻¹ : ↥(stab (puAmalgam c.pu.le) α)) : (puAmalgam c.pu.le).Universal) *
        ⁅w, (g : (puAmalgam c.pu.le).Universal) * v * (g : (puAmalgam c.pu.le).Universal)⁻¹⁆ *
        ((g⁻¹ : ↥(stab (puAmalgam c.pu.le) α)) : (puAmalgam c.pu.le).Universal)⁻¹ := by
    simp only [Subgroup.coe_inv, commutatorElement_def]
    group
  rw [e, natVecG_conj d.lh.nat g⁻¹ (hVU (Subgroup.commutator_mem_commutator hw hgv)), map_inv]

theorem natVecG_commutator_apply_zero (d : X3Data c α β γ ψ)
    (hVU : ⁅Vv (puAmalgam c.pu.le) α, Vv (puAmalgam c.pu.le) α⁆ ≤ Uloc c.pu.le L α)
    {z v : (puAmalgam c.pu.le).Universal} (hz : z ∈ ZM (puAmalgam c.pu.le) γ)
    (hv : v ∈ Vv (puAmalgam c.pu.le) α) : natVecG d.lh.nat ⁅z, v⁆ 0 = 0 := by
  have hU : ⁅z, v⁆ ∈ Uloc c.pu.le L α :=
    hVU (Subgroup.commutator_mem_commutator (d.zγVα hz) hv)
  have hS : ⁅z, v⁆ ∈ Usup (puAmalgam c.pu.le) α (((1 : ↥(stab (puAmalgam c.pu.le) α)) :
      (puAmalgam c.pu.le).Universal) • β) := by
    rw [Subgroup.coe_one, one_smul, ← d.uγ, Usup, zv_of_isMVtx _ d.mγ]
    exact Subgroup.commutator_mem_commutator hz (d.qαβ (d.lh.vq hv))
  have h := d.apply_zero_of_mem_usup (g := 1) (u := ⟨_, hU⟩) hS
  rw [map_one, inv_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at h
  rw [natVecG_of_mem d.lh.nat hU]
  exact h

theorem exists_natVecG_commutator_ne_zero (h467 : I467) (d : X3Data c α β γ ψ)
    (hVU : ⁅Vv (puAmalgam c.pu.le) α, Vv (puAmalgam c.pu.le) α⁆ ≤ Uloc c.pu.le L α)
    {z : (puAmalgam c.pu.le).Universal} (hz : z ∈ ZM (puAmalgam c.pu.le) γ)
    (hzα : z ∉ ZM (puAmalgam c.pu.le) α) :
    ∃ v ∈ Vv (puAmalgam c.pu.le) α, natVecG d.lh.nat ⁅z, v⁆ ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hzα
  have hzV : z ∈ Vv (puAmalgam c.pu.le) α := d.zγVα hz
  have hc : z ∈ Subgroup.centralizer (Vv (puAmalgam c.pu.le) α : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hU : ⁅z, v⁆ ∈ Uloc c.pu.le L α := hVU (Subgroup.commutator_mem_commutator hzV hv)
    have h1 : ⁅z, v⁆ = 1 :=
      natVecG_injective d.lh.nat hU (Subgroup.one_mem _) (by rw [hcon v hv, natVecG_one])
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  have hB : z ∈ Bloc c.pu.le L α := by
    rw [h467 G M T L F φ c α d.mα]
    exact ⟨hzV, hc⟩
  exact d.star ⟨d.zγstar hz, hB⟩

theorem exists_natVecG_commutator_eq (h467 : I467) (d : X3Data c α β γ ψ)
    (h2 : ∀ k : ↥(stab (puAmalgam c.pu.le) α), toSL3 ψ k ∈ (rootGroup 2 1 : Subgroup (SL3 F)) →
      ∀ z ∈ ZM (puAmalgam c.pu.le) γ, ⁅z, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ ZM _ α)
    (hVU : ⁅Vv (puAmalgam c.pu.le) α, Vv (puAmalgam c.pu.le) α⁆ ≤ Uloc c.pu.le L α)
    {z : (puAmalgam c.pu.le).Universal} (hz : z ∈ ZM (puAmalgam c.pu.le) γ)
    (hzα : z ∉ ZM (puAmalgam c.pu.le) α) {u : Fin 3 → F} (hu : u 0 = 0) :
    ∃ v ∈ Vv (puAmalgam c.pu.le) α, natVecG d.lh.nat ⁅z, v⁆ = u := by
  by_cases hu0 : u = 0
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [commutatorElement_one_right, natVecG_one, hu0]
  obtain ⟨v₀, hv₀, hne⟩ := exists_natVecG_commutator_ne_zero h467 d hVU hz hzα
  obtain ⟨A₀, hA₀, hA₀e⟩ := exists_stab_mulVec (natVecG d.lh.nat ⁅z, v₀⁆)
    (natVecG_commutator_apply_zero d hVU hz hv₀) hne
  obtain ⟨A, hA, hAe⟩ := exists_stab_mulVec u hu hu0
  obtain ⟨k, hk⟩ := toSL3_surjective d.lh.surj (A * A₀⁻¹)
  have hkrow : (toSL3 ψ k : Matrix (Fin 3) (Fin 3) F) 0 = Pi.single 0 1 := by
    rw [hk]
    exact row_mul_inv (by rw [hA, hA₀])
  refine ⟨(k : (puAmalgam c.pu.le).Universal) * v₀ * (k : (puAmalgam c.pu.le).Universal)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (d.lh.vN k.2) v₀).mp hv₀, ?_⟩
  rw [natVecG_commutator_conj d h2 hVU hz hv₀ hkrow, hk, ← hA₀e, Matrix.mulVec_mulVec,
    ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right, hAe]

theorem mem_qv_of_natVecG_commutator_eq_zero (h466a : I466a) (h467 : I467)
    (d : X3Data c α β γ ψ)
    (h2 : ∀ k : ↥(stab (puAmalgam c.pu.le) α), toSL3 ψ k ∈ (rootGroup 2 1 : Subgroup (SL3 F)) →
      ∀ z ∈ ZM (puAmalgam c.pu.le) γ, ⁅z, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ ZM _ α)
    (hVU : ⁅Vv (puAmalgam c.pu.le) α, Vv (puAmalgam c.pu.le) α⁆ ≤ Uloc c.pu.le L α)
    {z : (puAmalgam c.pu.le).Universal} (hz : z ∈ ZM (puAmalgam c.pu.le) γ)
    (hzα : z ∉ ZM (puAmalgam c.pu.le) α) {v : (puAmalgam c.pu.le).Universal}
    (hv : v ∈ Vv (puAmalgam c.pu.le) α) (h0 : natVecG d.lh.nat ⁅z, v⁆ = 0) :
    v ∈ Qv (puAmalgam c.pu.le) γ := by
  have hzV : z ∈ Vv (puAmalgam c.pu.le) α := d.zγVα hz
  have : Finite ↥(stab (puAmalgam c.pu.le) α) := d.lh.fin
  have : Finite ↥(Vv (puAmalgam c.pu.le) α) :=
    Finite.of_injective _ (Subgroup.inclusion_injective d.lh.vK)
  let Φ : ↥(Vv (puAmalgam c.pu.le) α) →* Multiplicative (Fin 3 → F) :=
    { toFun := fun x =>
        Multiplicative.ofAdd (natVecG d.lh.nat ⁅z, (x : (puAmalgam c.pu.le).Universal)⁆)
      map_one' := by
        simp only [Subgroup.coe_one, commutatorElement_one_right, natVecG_one]
        rfl
      map_mul' := fun x y => by
        simp only [Subgroup.coe_mul]
        rw [natVecG_commutator_mul_right d hVU hzV x.2 y.2]
        rfl }
  have hΦ : ∀ x : ↥(Vv (puAmalgam c.pu.le) α),
      Φ x = Multiplicative.ofAdd (natVecG d.lh.nat ⁅z, (x : (puAmalgam c.pu.le).Universal)⁆) :=
    fun _ => rfl
  have hQK : (Qv (puAmalgam c.pu.le) γ).subgroupOf (Vv (puAmalgam c.pu.le) α) ≤ Φ.ker := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [MonoidHom.mem_ker, hΦ]
    have h1 : ⁅z, (x : (puAmalgam c.pu.le).Universal)⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp
        (zm_le_centralizer_qv _ c.pu.hyp20 d.mγ hz) _ hx).symm
    rw [h1, natVecG_one]
    rfl
  have hrange : Fintype.card F ^ 2 ≤ Nat.card Φ.range := by
    have hinj : Function.Injective fun p : F × F =>
        (⟨Multiplicative.ofAdd ![0, p.1, p.2], by
          obtain ⟨w, hw, hwe⟩ := exists_natVecG_commutator_eq h467 d h2 hVU hz hzα
            (u := ![0, p.1, p.2]) rfl
          exact ⟨⟨w, hw⟩, by rw [hΦ, hwe]⟩⟩ : ↥Φ.range) := by
      intro p p' hpp
      have h : (![0, p.1, p.2] : Fin 3 → F) = ![0, p'.1, p'.2] := by
        simpa using congrArg Multiplicative.toAdd (congrArg Subtype.val hpp)
      exact Prod.ext (by simpa using congrFun h 1) (by simpa using congrFun h 2)
    have h := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_prod, Nat.card_eq_fintype_card, ← sq] at h
  have hidx : (Qv (puAmalgam c.pu.le) γ).relIndex (Vv (puAmalgam c.pu.le) α) ≤
      Fintype.card F ^ 2 := by
    rw [← h466a G M T L F φ c γ β d.mγ d.adjβγ.symm]
    refine Subgroup.relIndex_le_of_le_right (d.lh.vq.trans d.qαβ) ?_
    rw [h466a G M T L F φ c γ β d.mγ d.adjβγ.symm]
    positivity
  have hker : Φ.ker.index = Nat.card Φ.range := Subgroup.index_ker Φ
  have hQidx : ((Qv (puAmalgam c.pu.le) γ).subgroupOf (Vv (puAmalgam c.pu.le) α)).index =
      (Qv (puAmalgam c.pu.le) γ).relIndex (Vv (puAmalgam c.pu.le) α) := rfl
  have hmul := Subgroup.relIndex_mul_index hQK
  have hpos : Φ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hQpos : ((Qv (puAmalgam c.pu.le) γ).subgroupOf (Vv (puAmalgam c.pu.le) α)).index ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have hrel : ((Qv (puAmalgam c.pu.le) γ).subgroupOf (Vv (puAmalgam c.pu.le) α)).relIndex Φ.ker
      = 1 := by
    set r := ((Qv (puAmalgam c.pu.le) γ).subgroupOf (Vv (puAmalgam c.pu.le) α)).relIndex Φ.ker
    have h1 : r * Φ.ker.index ≤ 1 * Φ.ker.index := by
      rw [hmul, one_mul, hQidx, hker]
      exact hidx.trans hrange
    have h2' := Nat.le_of_mul_le_mul_right h1 (Nat.pos_of_ne_zero hpos)
    have h3 : r ≠ 0 := by
      intro h0
      apply hQpos
      rw [← hmul, h0, zero_mul]
    omega
  have hle := Subgroup.relIndex_eq_one.mp hrel
  have hx : (⟨v, hv⟩ : ↥(Vv (puAmalgam c.pu.le) α)) ∈ Φ.ker := by
    rw [MonoidHom.mem_ker, hΦ]
    simp only
    rw [h0]
    rfl
  have := hle hx
  rwa [Subgroup.mem_subgroupOf] at this

theorem exists_smul_natVecG_commutator [CharP F 2] (h466a : I466a) (h467 : I467)
    (d : X3Data c α β γ ψ)
    (h2 : ∀ k : ↥(stab (puAmalgam c.pu.le) α), toSL3 ψ k ∈ (rootGroup 2 1 : Subgroup (SL3 F)) →
      ∀ z ∈ ZM (puAmalgam c.pu.le) γ, ⁅z, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ ZM _ α)
    (hVU : ⁅Vv (puAmalgam c.pu.le) α, Vv (puAmalgam c.pu.le) α⁆ ≤ Uloc c.pu.le L α)
    {z : (puAmalgam c.pu.le).Universal} (hz : z ∈ ZM (puAmalgam c.pu.le) γ)
    (hzα : z ∉ ZM (puAmalgam c.pu.le) α) {z' : (puAmalgam c.pu.le).Universal}
    (hz' : z' ∈ ZM (puAmalgam c.pu.le) γ) :
    ∃ a : F, ∀ v ∈ Vv (puAmalgam c.pu.le) α,
      natVecG d.lh.nat ⁅z', v⁆ = a • natVecG d.lh.nat ⁅z, v⁆ := by
  have hzV : z ∈ Vv (puAmalgam c.pu.le) α := d.zγVα hz
  have hz'V : z' ∈ Vv (puAmalgam c.pu.le) α := d.zγVα hz'
  have key : ∀ v ∈ Vv (puAmalgam c.pu.le) α, ∀ w ∈ Vv (puAmalgam c.pu.le) α,
      natVecG d.lh.nat ⁅z, v⁆ = natVecG d.lh.nat ⁅z, w⁆ →
        natVecG d.lh.nat ⁅z', v⁆ = natVecG d.lh.nat ⁅z', w⁆ := by
    intro v hv w hw he
    have hvw : v⁻¹ * w ∈ Vv (puAmalgam c.pu.le) α :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hv) hw
    have h0 : natVecG d.lh.nat ⁅z, v⁻¹ * w⁆ = 0 := by
      rw [natVecG_commutator_inv_mul d hVU hzV hv hw, he, sub_self]
    have hQ := mem_qv_of_natVecG_commutator_eq_zero h466a h467 d h2 hVU hz hzα hvw h0
    have h1 : ⁅z', v⁻¹ * w⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp
        (zm_le_centralizer_qv _ c.pu.hyp20 d.mγ hz') _ hQ).symm
    have h1' := natVecG_commutator_inv_mul d hVU hz'V hv hw
    rw [h1, natVecG_one] at h1'
    exact (sub_eq_zero.mp h1'.symm).symm
  obtain ⟨v₁, hv₁, hv₁e⟩ := exists_natVecG_commutator_eq h467 d h2 hVU hz hzα
    (u := Pi.single 1 1) (by simp)
  set a := natVecG d.lh.nat ⁅z', v₁⁆ 1 with ha
  refine ⟨a, ?_⟩
  have hv₁' : natVecG d.lh.nat ⁅z', v₁⁆ = a • (Pi.single 1 1 : Fin 3 → F) := by
    obtain ⟨k, hk⟩ := toSL3_surjective d.lh.surj (rootElt 1 2 1)
    have hkrow : (toSL3 ψ k : Matrix (Fin 3) (Fin 3) F) 0 = Pi.single 0 1 := by
      rw [hk]
      exact rootElt_row_zero (by decide) 1
    have hkv : (k : (puAmalgam c.pu.le).Universal) * v₁ * (k : (puAmalgam c.pu.le).Universal)⁻¹ ∈
        Vv (puAmalgam c.pu.le) α := (Subgroup.mem_normalizer_iff.mp (d.lh.vN k.2) v₁).mp hv₁
    have h1 : natVecG d.lh.nat ⁅z, (k : (puAmalgam c.pu.le).Universal) * v₁ *
        (k : (puAmalgam c.pu.le).Universal)⁻¹⁆ = natVecG d.lh.nat ⁅z, v₁⁆ := by
      rw [natVecG_commutator_conj d h2 hVU hz hv₁ hkrow, hv₁e, hk,
        rootElt_mulVec (show (1 : Fin 3) ≠ 2 by decide)]
      simp
    have h2' := key _ hkv _ hv₁ h1
    rw [natVecG_commutator_conj d h2 hVU hz' hv₁ hkrow, hk,
      rootElt_mulVec (show (1 : Fin 3) ≠ 2 by decide)] at h2'
    have h3 : natVecG d.lh.nat ⁅z', v₁⁆ 2 = 0 := by
      have := congrFun h2' 1
      simpa using this
    have h0 := natVecG_commutator_apply_zero d hVU hz' hv₁
    funext i
    fin_cases i
    · simp [h0]
    · simp [ha]
    · simp [h3]
  intro v hv
  by_cases hu : natVecG d.lh.nat ⁅z, v⁆ = 0
  · have h := key v hv 1 (Subgroup.one_mem _)
      (by rw [hu, commutatorElement_one_right, natVecG_one])
    rw [h, commutatorElement_one_right, natVecG_one, hu, smul_zero]
  · obtain ⟨A, hA, hAe⟩ := exists_stab_mulVec (natVecG d.lh.nat ⁅z, v⁆)
      (natVecG_commutator_apply_zero d hVU hz hv) hu
    obtain ⟨k, hk⟩ := toSL3_surjective d.lh.surj A
    have hkrow : (toSL3 ψ k : Matrix (Fin 3) (Fin 3) F) 0 = Pi.single 0 1 := by rw [hk, hA]
    have hkv : (k : (puAmalgam c.pu.le).Universal) * v₁ * (k : (puAmalgam c.pu.le).Universal)⁻¹ ∈
        Vv (puAmalgam c.pu.le) α := (Subgroup.mem_normalizer_iff.mp (d.lh.vN k.2) v₁).mp hv₁
    have h1 : natVecG d.lh.nat ⁅z, v⁆ = natVecG d.lh.nat ⁅z, (k : (puAmalgam c.pu.le).Universal) *
        v₁ * (k : (puAmalgam c.pu.le).Universal)⁻¹⁆ := by
      rw [natVecG_commutator_conj d h2 hVU hz hv₁ hkrow, hv₁e, hk, hAe]
    rw [key v hv _ hkv h1, natVecG_commutator_conj d h2 hVU hz' hv₁ hkrow, hv₁', hk,
      Matrix.mulVec_smul, hAe]

theorem exists_natVecG_commutator_smul [CharP F 2] (h465 : I465) (h466a : I466a) (h467 : I467)
    (d : X3Data c α β γ ψ)
    (h2 : ∀ k : ↥(stab (puAmalgam c.pu.le) α), toSL3 ψ k ∈ (rootGroup 2 1 : Subgroup (SL3 F)) →
      ∀ z ∈ ZM (puAmalgam c.pu.le) γ, ⁅z, (k : (puAmalgam c.pu.le).Universal)⁆ ∈ ZM _ α)
    (hVU : ⁅Vv (puAmalgam c.pu.le) α, Vv (puAmalgam c.pu.le) α⁆ ≤ Uloc c.pu.le L α)
    {z : (puAmalgam c.pu.le).Universal} (hz : z ∈ ZM (puAmalgam c.pu.le) γ)
    (hzα : z ∉ ZM (puAmalgam c.pu.le) α) (s : F) :
    ∃ z' ∈ ZM (puAmalgam c.pu.le) γ, ∀ v ∈ Vv (puAmalgam c.pu.le) α,
      natVecG d.lh.nat ⁅z', v⁆ = s • natVecG d.lh.nat ⁅z, v⁆ := by
  have hzV : z ∈ Vv (puAmalgam c.pu.le) α := d.zγVα hz
  obtain ⟨v₁, hv₁, hv₁e⟩ := exists_natVecG_commutator_eq h467 d h2 hVU hz hzα
    (u := Pi.single 1 1) (by simp)
  have hsc : ∀ z' ∈ ZM (puAmalgam c.pu.le) γ, ∀ v ∈ Vv (puAmalgam c.pu.le) α,
      natVecG d.lh.nat ⁅z', v⁆ = natVecG d.lh.nat ⁅z', v₁⁆ 1 • natVecG d.lh.nat ⁅z, v⁆ := by
    intro z' hz' v hv
    obtain ⟨a, ha⟩ := exists_smul_natVecG_commutator h466a h467 d h2 hVU hz hzα hz'
    have h1 := ha v₁ hv₁
    rw [hv₁e] at h1
    have h2' : natVecG d.lh.nat ⁅z', v₁⁆ 1 = a := by rw [h1]; simp
    rw [h2']
    exact ha v hv
  let χ : ↥(ZM (puAmalgam c.pu.le) γ) →* Multiplicative F :=
    { toFun := fun x => Multiplicative.ofAdd
        (natVecG d.lh.nat ⁅(x : (puAmalgam c.pu.le).Universal), v₁⁆ 1)
      map_one' := by
        simp only [Subgroup.coe_one, commutatorElement_one_left, natVecG_one]
        rfl
      map_mul' := fun x y => by
        simp only [Subgroup.coe_mul]
        rw [natVecG_commutator_mul_left d hVU (d.zγVα x.2) (d.zγVα y.2) hv₁]
        rfl }
  have hχ : ∀ x : ↥(ZM (puAmalgam c.pu.le) γ), χ x =
      Multiplicative.ofAdd (natVecG d.lh.nat ⁅(x : (puAmalgam c.pu.le).Universal), v₁⁆ 1) :=
    fun _ => rfl
  have hker : χ.ker ≤ (ZH (puAmalgam c.pu.le) β).subgroupOf (ZM (puAmalgam c.pu.le) γ) := by
    intro x hx
    rw [MonoidHom.mem_ker, hχ] at hx
    have hx0 : natVecG d.lh.nat ⁅(x : (puAmalgam c.pu.le).Universal), v₁⁆ 1 = 0 := hx
    have hxα : (x : (puAmalgam c.pu.le).Universal) ∈ ZM (puAmalgam c.pu.le) α := by
      by_contra hxα
      obtain ⟨v, hv, hne⟩ := exists_natVecG_commutator_ne_zero h467 d hVU x.2 hxα
      apply hne
      rw [hsc _ x.2 v hv, hx0, zero_smul]
    rw [Subgroup.mem_subgroupOf]
    refine I464.mem_zh_of_mem_zm c.pu d.mα d.adjαβ hxα ?_
    rw [Subgroup.mem_centralizer_iff]
    have hT : Qv (puAmalgam c.pu.le) β ≤
        Subgroup.centralizer ({(x : (puAmalgam c.pu.le).Universal)} : Set _) := by
      rw [← d.tγ]
      refine sup_le (fun t ht => ?_) (fun t ht => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        rintro _ rfl
        exact (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ c.pu.hyp20 d.mγ x.2) t
          (vv_le_qv c.pu (critDist_gt_two c) d.mγ ht)).symm
      · rw [Subgroup.mem_centralizer_iff]
        rintro _ rfl
        exact (Subgroup.mem_centralizer_iff.mp (d.lh.zq hxα) t ht).symm
    intro t ht
    exact (Subgroup.mem_centralizer_iff.mp (hT ht) _ rfl).symm
  have : Finite ↥(stab (puAmalgam c.pu.le) α) := d.lh.fin
  have : Finite ↥(ZM (puAmalgam c.pu.le) γ) :=
    Finite.of_injective _ (Subgroup.inclusion_injective d.zγK)
  have hidx : Fintype.card F ≤ χ.ker.index := by
    rw [← (h465 G M T L F φ c γ β d.mγ d.adjβγ.symm).2.1]
    exact Subgroup.index_antitone hker
  have hrange : χ.range = ⊤ := by
    refine Subgroup.eq_top_of_le_card _ ?_
    rw [← Subgroup.index_ker χ, Nat.card_eq_fintype_card]
    simpa using hidx
  obtain ⟨x, hx⟩ := (MonoidHom.range_eq_top.mp hrange) (Multiplicative.ofAdd s)
  refine ⟨x, x.2, fun v hv => ?_⟩
  rw [hsc _ x.2 v hv]
  rw [hχ] at hx
  rw [show natVecG d.lh.nat ⁅(x : (puAmalgam c.pu.le).Universal), v₁⁆ 1 = s from
    Multiplicative.ofAdd.injective hx]

end CFSG.Quasithin.MS93.S46.KCF
