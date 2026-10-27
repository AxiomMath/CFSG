module

public import CFSG.Quasithin.Background.E6TwentyThreePA
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19USp4Aut

public section

namespace CFSG.Quasithin.E6

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped Pointwise

section Unipotent

variable {F : Type} [Field F]

@[expose] def zMat (α β : F) : Matrix (Fin 2) (Fin 2) F := !![α, β; β, 0]

theorem zMat_transpose (α β : F) : (zMat α β)ᵀ = zMat α β := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem inv_mul_zMat_mul_inv_transpose [CharP F 2] {A : Matrix (Fin 2) (Fin 2) F}
    (hA : IsUnitriangular A) (α β : F) : A⁻¹ * zMat α β * A⁻¹ᵀ = zMat α β := by
  have h10 : A 1 0 = 0 := hA.1 (by decide)
  have h00 : A 0 0 = 1 := hA.2 0
  have h11 : A 1 1 = 1 := hA.2 1
  have hAe : A = !![1, A 0 1; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]
  set t := A 0 1
  have hinv : A⁻¹ = !![1, -t; 0, 1] := by
    rw [hAe]
    apply Matrix.inv_eq_left_inv
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  linear_combination (-t * β) * h2

@[expose] noncomputable def zElt (α β : F) : StatedSp 2 F :=
  upperUnipotentSp 2 F (zMat_transpose α β)

theorem coe_zElt (α β : F) :
    (((zElt α β : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = blockMat 1 (zMat α β) := by
  rw [zElt, coe_upperUnipotentSp]
  simp [blockMat]

theorem zElt_mem_unipotent (α β : F) : zElt α β ∈ unipotent 2 F :=
  ⟨1, zMat α β, ⟨fun i j hij => Matrix.one_apply_ne (by rintro rfl; exact lt_irrefl _ hij),
    fun i => Matrix.one_apply_eq i⟩, zMat_transpose α β, coe_zElt α β⟩

theorem zElt_mul_comm [CharP F 2] (α β : F) {u : StatedSp 2 F} (hu : u ∈ unipotent 2 F) :
    zElt α β * u = u * zElt α β := by
  obtain ⟨A, C, hA, -, hu'⟩ := hu
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_zElt, hu', blockMat_mul hA.isUnit_det, blockMat_mul (by simp), Matrix.one_mul,
    Matrix.mul_one, inv_mul_zMat_mul_inv_transpose hA, inv_one, transpose_one, Matrix.one_mul,
    Matrix.mul_one, add_comm]

theorem zElt_injective : Function.Injective fun p : F × F => zElt p.1 p.2 := by
  rintro ⟨α, β⟩ ⟨α', β'⟩ h
  have h1 := congrArg (fun g : StatedSp 2 F => ((g : GL (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) h
  simp only [coe_zElt] at h1
  have hα := congrFun (congrFun h1 (Sum.inl 0)) (Sum.inr 0)
  have hβ := congrFun (congrFun h1 (Sum.inl 0)) (Sum.inr 1)
  simp [blockMat, zMat] at hα hβ
  rw [hα, hβ]

theorem sixteen_le_card_center_unipotent [CharP F 2] [Finite F] (hF : Nat.card F = 4) :
    16 ≤ Nat.card ↥(Subgroup.center ↥(unipotent 2 F)) := by
  let ι : F × F → ↥(Subgroup.center ↥(unipotent 2 F)) := fun p =>
    ⟨⟨zElt p.1 p.2, zElt_mem_unipotent p.1 p.2⟩, Subgroup.mem_center_iff.mpr fun u =>
      Subtype.ext (zElt_mul_comm p.1 p.2 u.2).symm⟩
  have hι : Function.Injective ι := fun p q hpq =>
    zElt_injective (congrArg (fun z : ↥(Subgroup.center ↥(unipotent 2 F)) =>
      ((z : ↥(unipotent 2 F)) : StatedSp 2 F)) hpq)
  have h := Nat.card_le_card_of_injective ι hι
  rwa [Nat.card_prod, hF] at h

end Unipotent

section Centralizer

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem thirtyTwo_le_card_centralizer_of_center {Q : Type*} [Group Q] [Finite Q]
    (h256 : 32 ≤ Nat.card Q) (hZ : 16 ≤ Nat.card ↥(Subgroup.center Q))
    (q : Q) : 32 ≤ Nat.card ↥(Subgroup.centralizer ({q} : Set Q)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hq : q ∈ Subgroup.center Q
  · have htop : Subgroup.centralizer ({q} : Set Q) = ⊤ := by
      rw [eq_top_iff]
      intro g _
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hq g)
    rw [htop, Subgroup.card_top]
    exact h256
  · set Z := Subgroup.center Q
    set W := Z ⊔ Subgroup.zpowers q
    have hZW : Z < W := lt_of_le_of_ne le_sup_left fun h =>
      hq (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers q))
    have hWC : W ≤ Subgroup.centralizer ({q} : Set Q) := sup_le
      (fun z hz => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_center_iff.mp hz q).symm)
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
    have hmul := Subgroup.relIndex_mul_card (H := Z) (K := W)
    rw [inf_eq_left.mpr hZW.le] at hmul
    have hidx : 2 ≤ Z.relIndex W := by
      have h1 : Z.relIndex W ≠ 1 := fun h1 =>
        hZW.ne (le_antisymm hZW.le ((Subgroup.relIndex_eq_one).1 h1))
      have h0 : Z.relIndex W ≠ 0 := fun h0 => by
        rw [h0, zero_mul] at hmul
        exact (Nat.card_pos (α := W)).ne hmul
      omega
    have hW : 32 ≤ Nat.card W := by nlinarith
    exact hW.trans (Subgroup.card_le_of_le hWC)

theorem thirtyTwo_dvd_card_centralizer_sp (hF : Nat.card F = 4) (s : StatedSp 2 F)
    (hs : IsPGroup 2 (Subgroup.zpowers s)) :
    2 ^ 5 ∣ Nat.card ↥(Subgroup.centralizer ({s} : Set (StatedSp 2 F))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF' : Nat.card F = 2 ^ 2 := by rw [hF]; norm_num
  obtain ⟨U, hU⟩ := exists_sylow_unipotent (K := F) 2 2
  obtain ⟨Q, hQ⟩ := hs.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (StatedSp 2 F) U Q
  have hcardU : Nat.card ↥(unipotent 2 F) = 256 := by
    rw [card_unipotent, hF]; norm_num
  have hQU : (Q : Subgroup (StatedSp 2 F)) = MulAut.conj c • unipotent 2 F := by
    rw [← hc, Sylow.coe_subgroup_smul, hU]
  let eQ : ↥(Q : Subgroup (StatedSp 2 F)) ≃* ↥(unipotent 2 F) :=
    (MulEquiv.subgroupCongr hQU).trans (Subgroup.equivSMul (MulAut.conj c) (unipotent 2 F)).symm
  have hQ2 : IsPGroup 2 ↥(Q : Subgroup (StatedSp 2 F)) := Q.isPGroup'
  have hcardQ : Nat.card ↥(Q : Subgroup (StatedSp 2 F)) = 256 := by
    rw [Nat.card_congr eQ.toEquiv, hcardU]
  have hZQ : 16 ≤ Nat.card ↥(Subgroup.center ↥(Q : Subgroup (StatedSp 2 F))) := by
    have h1 := Subgroup.card_map_of_injective
      (K := Subgroup.center ↥(Q : Subgroup (StatedSp 2 F)))
      (f := (eQ : ↥(Q : Subgroup (StatedSp 2 F)) →* ↥(unipotent 2 F))) eQ.injective
    rw [Subgroup.map_center_eq eQ] at h1
    rw [← h1]
    exact sixteen_le_card_center_unipotent hF
  have hsQ : s ∈ (Q : Subgroup (StatedSp 2 F)) := hQ (Subgroup.mem_zpowers s)
  have h32 := thirtyTwo_le_card_centralizer_of_center (by rw [hcardQ]; norm_num) hZQ
    ⟨s, hsQ⟩
  set CQ := Subgroup.centralizer ({(⟨s, hsQ⟩ : ↥(Q : Subgroup (StatedSp 2 F)))} :
    Set ↥(Q : Subgroup (StatedSp 2 F))) with hCQ
  have hmap : CQ.map (Q : Subgroup (StatedSp 2 F)).subtype ≤
      Subgroup.centralizer ({s} : Set (StatedSp 2 F)) := by
    rintro _ ⟨g, hg, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp hg
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val this)
  have hcardCQ : Nat.card ↥(CQ.map (Q : Subgroup (StatedSp 2 F)).subtype) = Nat.card CQ :=
    Subgroup.card_map_of_injective Subtype.coe_injective
  have hCQ2 : IsPGroup 2 ↥CQ := hQ2.to_subgroup CQ
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hCQ2
  have hm5 : 5 ≤ m := by
    by_contra h5
    push Not at h5
    have : 2 ^ m ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hm] at this
    omega
  calc 2 ^ 5 ∣ 2 ^ m := Nat.pow_dvd_pow 2 hm5
    _ = Nat.card ↥(CQ.map (Q : Subgroup (StatedSp 2 F)).subtype) := by rw [hcardCQ, hm]
    _ ∣ _ := Subgroup.card_dvd_of_le hmap

theorem thirtyTwo_dvd_card_centralizer (hF : Nat.card F = 4) (s : StatedProj (StatedSp 2 F))
    (hs : IsPGroup 2 (Subgroup.zpowers s)) :
    2 ^ 5 ∣ Nat.card ↥(Subgroup.centralizer ({s} : Set (StatedProj (StatedSp 2 F)))) := by
  have hbij := UnitaryHigher.proj_bijective_of_charTwo (r := 2) (K := F)
  let e : StatedSp 2 F ≃* StatedProj (StatedSp 2 F) := MulEquiv.ofBijective (proj 2 F) hbij
  set s' := e.symm s with hs'
  have hs'2 : IsPGroup 2 (Subgroup.zpowers s') := by
    have := hs.map e.symm.toMonoidHom
    rwa [MonoidHom.map_zpowers] at this
  have h := thirtyTwo_dvd_card_centralizer_sp hF s' hs'2
  have hmap : (Subgroup.centralizer ({s'} : Set (StatedSp 2 F))).map e.toMonoidHom =
      Subgroup.centralizer ({s} : Set (StatedProj (StatedSp 2 F))) := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hv
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := congrArg e hv
      rw [map_mul, map_mul, hs', MulEquiv.apply_symm_apply] at h1
      exact h1
    · intro hw
      refine ⟨e.symm w, ?_, by simp⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hw
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rw [hs', ← map_mul, ← map_mul, hw]
  rw [← hmap, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
  exact h

end Centralizer

theorem card_fixedSub_conj {M : Type*} [Group M] (α γ : MulAut M) :
    Nat.card ↥(Id2519.USp4.fixedSub (γ * α * γ⁻¹)) = Nat.card ↥(Id2519.USp4.fixedSub α) := by
  have hfwd : ∀ p : M, (γ * α * γ⁻¹) p = p → α (γ⁻¹ p) = γ⁻¹ p := fun p hp => by
    have h1 : γ (α (γ⁻¹ p)) = p := hp
    calc α (γ⁻¹ p) = γ⁻¹ (γ (α (γ⁻¹ p))) := (MulAut.inv_apply_self M γ _).symm
      _ = γ⁻¹ p := by rw [h1]
  have hbwd : ∀ q : M, α q = q → (γ * α * γ⁻¹) (γ q) = γ q := fun q hq => by
    show γ (α (γ⁻¹ (γ q))) = γ q
    rw [MulAut.inv_apply_self, hq]
  exact Nat.card_congr
    { toFun := fun p => ⟨γ⁻¹ p, hfwd p p.2⟩
      invFun := fun q => ⟨γ q, hbwd q q.2⟩
      left_inv := fun p => Subtype.ext (by simp)
      right_inv := fun q => Subtype.ext (by simp) }

namespace InspHyp

variable {G : Type} [Group G] [Finite G] {Y E X : Subgroup G} {a z : G}

theorem false_of_patSp4 (h : InspHyp Y E X a z) (hSp : Id2519.PatSp4 Y X)
    (h8 : (E ⊓ Subgroup.centralizer (Y : Set G)).relIndex E = 8) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hmodel⟩ := hSp
  obtain ⟨-, F, _, _, hF, ⟨φ0⟩⟩ := id hmodel
  obtain ⟨φ⟩ : Nonempty (↥Y ≃* StatedProj (StatedSp 2 F)) := ⟨φ0⟩
  have hF4 : Nat.card F = 4 := by rw [hF]; norm_num
  have : CharP F 2 := by
    have : Fintype F := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hF])
  have hcP : Subgroup.center (StatedProj (StatedSp 2 F)) = ⊥ := by
    rw [eq_bot_iff]
    intro p hp
    exact Id2519.USp4.eq_one_of_central fun q => (Subgroup.mem_center_iff.mp hp q).symm
  have hc : Subgroup.center ↥Y = ⊥ := by
    have h1 := Subgroup.map_center_eq φ.symm
    rw [hcP, Subgroup.map_bot] at h1
    exact h1.symm
  have hperf : Group.IsPerfect ↥Y := h.quasi.1
  have hker : φ.toMonoidHom.ker = Subgroup.center ↥Y := by
    rw [hc, MonoidHom.ker_eq_bot_iff]
    exact φ.injective
  have hcardE := card_map_quotAction φ.toMonoidHom φ.surjective hker hperf h.norm
  rw [h8] at hcardE
  set ψ := quotAction φ.toMonoidHom φ.surjective hker with hψ
  set Ebar := (E.subgroupOf (Subgroup.normalizer (Y : Set G))).map ψ with hEbar
  have hsq : ∀ x : ↥(Subgroup.normalizer (Y : Set G)), (x : G) ∈ E → ψ x * ψ x = 1 := by
    intro x hx
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (h.mul_self_eq_one hx)
    rw [this, map_one]
  obtain ⟨hinv, -, -⟩ := Id2519.USp4.aut_facts (F := F) hF4
  have hEsemi : Ebar ≤ spSemilinearAutGroup 2 F := by
    rintro _ ⟨x, hx, rfl⟩
    by_cases h1 : ψ x = 1
    · rw [h1]; exact Subgroup.one_mem _
    · refine hinv _ (orderOf_eq_prime ?_ h1)
      rw [pow_two]
      exact hsq x hx
  obtain ⟨hID, -⟩ := standard_outer_quotient (K := F) (r := 2) (by norm_num)
  have hrel1 : (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp 2 F))).relIndex (spLinearAutGroup 2 F) = 1 := by
    have h := relIndex_inner_spLinearAutGroup_dvd (r := 2) Nat.prime_two (by norm_num : 1 ≤ 2) hF
    have hg : Nat.gcd 2 (2 ^ 2 - 1) = 1 := by norm_num
    rw [hg] at h
    exact Nat.dvd_one.mp h
  have hrel2 := relIndex_spLinearAutGroup_dvd (r := 2) Nat.prime_two (by norm_num : 1 ≤ 2) hF
  have hrelE : (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp 2 F))).relIndex (spSemilinearAutGroup 2 F) ≤ 2 := by
    rw [← Subgroup.relIndex_mul_relIndex
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSp 2 F)))
      (spLinearAutGroup 2 F) (spSemilinearAutGroup 2 F) hID
      spLinearAutGroup_le_spSemilinearAutGroup, hrel1, one_mul]
    exact Nat.le_of_dvd (by norm_num) hrel2
  have hrelE0 : (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp 2 F))).relIndex (spSemilinearAutGroup 2 F) ≠ 0 := by
    rw [← Subgroup.relIndex_mul_relIndex
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSp 2 F)))
      (spLinearAutGroup 2 F) (spSemilinearAutGroup 2 F) hID
      spLinearAutGroup_le_spSemilinearAutGroup, hrel1, one_mul]
    intro h0
    rw [h0] at hrel2
    exact absurd (Nat.eq_zero_of_zero_dvd hrel2) (by norm_num)
  have hA : 4 ≤ Nat.card ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp 2 F)) ⊓ Ebar) := by
    have hle := (Subgroup.relIndex_le_of_le_right hEsemi hrelE0).trans hrelE
    have hmul := Subgroup.relIndex_mul_card
      (H := CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSp 2 F)))
      (K := Ebar)
    rw [hcardE] at hmul
    have hpos : 0 < (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (StatedProj (StatedSp 2 F))).relIndex Ebar :=
      Nat.pos_of_ne_zero fun h0 => by rw [h0, zero_mul] at hmul; exact absurd hmul (by norm_num)
    interval_cases hr : (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp 2 F))).relIndex Ebar <;> omega
  obtain ⟨w, hw, hw1⟩ : ∃ w ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp 2 F)) ⊓ Ebar, w ≠ 1 := by
    by_contra hall
    push Not at hall
    have hbot : CFSG.ComponentClassification.OuterAutomorphisms.inner
        (StatedProj (StatedSp 2 F)) ⊓ Ebar = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hall
    rw [hbot, Subgroup.card_bot] at hA
    omega
  obtain ⟨x, hxE, hxw⟩ := hw.2
  obtain ⟨s, hs⟩ := hw.1
  have hxE' : (x : G) ∈ E := hxE
  have hs2 : s * s = 1 := by
    have hww : w * w = 1 := by rw [← hxw]; exact hsq x hxE'
    apply Id2519.USp4.eq_one_of_central
    intro g
    have h1 := congrArg (fun α : MulAut (StatedProj (StatedSp 2 F)) => α g) hww
    simp only [← hs, MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply] at h1
    have h2 : s * s * g * (s * s)⁻¹ = g := by
      rw [show s * s * g * (s * s)⁻¹ = s * (s * g * s⁻¹) * s⁻¹ by group]
      exact h1
    calc s * s * g = s * s * g * (s * s)⁻¹ * (s * s) := by group
      _ = g * (s * s) := by rw [h2]
  have hcardx : Nat.card ↥(Y ⊓ Subgroup.centralizer ({(x : G)} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({s} : Set (StatedProj (StatedSp 2 F)))) := by
    have hcent : ∀ y : ↥Y, (y : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) ↔
        φ y ∈ Subgroup.centralizer ({s} : Set (StatedProj (StatedSp 2 F))) := by
      intro y
      rw [mem_centralizer_iff_quotAction φ.toMonoidHom φ.surjective hker hc x y,
        Subgroup.mem_centralizer_singleton_iff]
      change ψ x (φ y) = φ y ↔ _
      rw [hxw, ← hs, MulAut.conj_apply]
      constructor
      · intro h1
        calc φ y * s = s * φ y * s⁻¹ * s := by rw [h1]
          _ = s * φ y := by group
      · intro h1
        rw [← h1]
        group
    have hmapC : ((Y ⊓ Subgroup.centralizer ({(x : G)} : Set G)).subgroupOf Y).map
        φ.toMonoidHom = Subgroup.centralizer ({s} : Set (StatedProj (StatedSp 2 F))) := by
      ext w'
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (hcent y).1 (Subgroup.mem_subgroupOf.mp hy).2
      · intro hw'
        refine ⟨φ.symm w', Subgroup.mem_subgroupOf.mpr ⟨(φ.symm w').2, (hcent _).2 ?_⟩, ?_⟩
        · simpa using hw'
        · simp
    rw [← hmapC, Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  have hs2' : IsPGroup 2 (Subgroup.zpowers s) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hs2)
  have hx32 : 5 ≤ (Nat.card ↥(Y ⊓ Subgroup.centralizer ({(x : G)} : Set G))).factorization 2 := by
    rw [hcardx]
    exact (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').1
      (thirtyTwo_dvd_card_centralizer hF4 s hs2')
  have hxY : ¬ Y ≤ Subgroup.centralizer ({(x : G)} : Set G) := by
    intro hle
    apply hw1
    rw [← hxw]
    exact (quotAction_eq_one_iff _ _ hker hperf x).mpr (Subgroup.mem_centralizer_iff.mpr
      fun y hy => Subgroup.mem_centralizer_singleton_iff.mp (hle hy))
  have hfle := h.factorization_le hxE' hxY
  set aN : ↥(Subgroup.normalizer (Y : Set G)) := ⟨a, h.norm h.mem⟩ with haN
  have hfixa : ∀ y : ↥Y, (y : G) ∈ Subgroup.centralizer ({a} : Set G) ↔
      φ y ∈ Id2519.USp4.fixedSub (ψ aN) := fun y =>
    mem_centralizer_iff_quotAction φ.toMonoidHom φ.surjective hker hc aN y
  have hmapA : ((Y ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf Y).map φ.toMonoidHom =
      Id2519.USp4.fixedSub (ψ aN) := by
    ext w'
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hfixa y).1 (Subgroup.mem_subgroupOf.mp hy).2
    · intro hw'
      refine ⟨φ.symm w', Subgroup.mem_subgroupOf.mpr ⟨(φ.symm w').2, (hfixa _).2 ?_⟩, ?_⟩
      · simpa using hw'
      · simp
  have hcardA : Nat.card ↥(Y ⊓ Subgroup.centralizer ({a} : Set G)) =
      Nat.card ↥(Id2519.USp4.fixedSub (ψ aN)) := by
    rw [← hmapA, Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  have hψa2 : ψ aN * ψ aN = 1 := hsq aN h.mem
  have hψa1 : ψ aN ≠ 1 := by
    intro h1
    have h1' := (quotAction_eq_one_iff _ _ hker hperf aN).mp h1
    exact h.not_cent fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp h1' y hy)
  have hψaO : ψ aN ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSp 2 F)) := by
    rintro ⟨sa, hsa⟩
    apply hψa1
    have hsa2 : sa ^ 2 = 1 := by
      rw [pow_two]
      apply Id2519.USp4.eq_one_of_central
      intro g
      have h1 := congrArg (fun α : MulAut (StatedProj (StatedSp 2 F)) => α g) hψa2
      simp only [← hsa, MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply] at h1
      have h2 : sa * sa * g * (sa * sa)⁻¹ = g := by
        rw [show sa * sa * g * (sa * sa)⁻¹ = sa * (sa * g * sa⁻¹) * sa⁻¹ by group]
        exact h1
      calc sa * sa * g = sa * sa * g * (sa * sa)⁻¹ * (sa * sa) := by group
        _ = g * (sa * sa) := by rw [h2]
    set Kb := (X.subgroupOf Y).map φ.toMonoidHom with hKb
    have hXY : X ≤ Y := h.comp.1.trans inf_le_left
    have h9 : 9 ∣ Nat.card ↥Kb := by
      rw [hKb, Subgroup.card_map_of_injective φ.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXY).toEquiv, h.card_X]
      norm_num
    have hsa1 := Id2519.USp4.eq_one_of_centralizes_of_nine_dvd hF4 h9 hsa2 (by
      rintro _ ⟨y, hy, rfl⟩
      have hya : (y : G) ∈ Subgroup.centralizer ({a} : Set G) :=
        (h.comp.1 (Subgroup.mem_subgroupOf.mp hy)).2
      have h1 := (hfixa y).1 hya
      rw [Id2519.USp4.mem_fixedSub, ← hsa, MulAut.conj_apply] at h1
      change sa * φ y = φ y * sa
      calc sa * φ y = sa * φ y * sa⁻¹ * sa := by group
        _ = φ y * sa := by rw [h1])
    rw [← hsa, hsa1, map_one]
  have hψaE : ψ aN ∈ spSemilinearAutGroup 2 F := hEsemi ⟨aN, h.mem, rfl⟩
  obtain ⟨σ, hh, hσ1, hσσ, hτ⟩ := Id2519.USp4.exists_conj_fieldAut hF4 hψa2 hψaO hψaE
  have h720 : Nat.card ↥(Id2519.USp4.fixedSub (ψ aN)) = 720 := by
    rw [hτ, card_fixedSub_conj, Id2519.USp4.card_fixedSub_fieldAut hF4 hσ1 hσσ]
  have ha4 : (Nat.card ↥(Y ⊓ Subgroup.centralizer ({a} : Set G))).factorization 2 < 5 := by
    rw [hcardA, h720]
    by_contra hge
    push Not at hge
    have := (Nat.prime_two.pow_dvd_iff_le_factorization (by norm_num : (720 : ℕ) ≠ 0)).2 hge
    omega
  omega

end InspHyp

end CFSG.Quasithin.E6
