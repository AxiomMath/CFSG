module

public import CFSG.Quasithin.H13.A6Setting4
public import CFSG.Quasithin.H13.A6Producer134
public import CFSG.Quasithin.H13.A6Assembly

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

theorem mem_zpowers_allOnes {x : P6} : x ∈ Subgroup.zpowers (G6.allOnes 6) ↔
    x = 1 ∨ x = G6.allOnes 6 := by
  constructor
  · rintro ⟨k, rfl⟩
    have h2 : orderOf (G6.allOnes 6) = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [pow_two]; exact allOnes_mul_self) allOnes_ne_one
    show G6.allOnes 6 ^ k = 1 ∨ G6.allOnes 6 ^ k = G6.allOnes 6
    rw [← zpow_mod_orderOf, h2]
    have : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
    rcases this with h | h <;> rw [h]
    · left; exact zpow_zero _
    · right; exact zpow_one _
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem nrm_eq_one_iff : ∀ x : P6, nrm x = 1 ↔ (x = 1 ∨ x = G6.allOnes 6) := by
  decide +kernel

@[expose] def nrmHom : ↥(FFModel.altDn 6).sec →* ↥W4 where
  toFun x := ⟨nrm (show P6 from x.1), inW4_nrm _ (G6.mem_coreMod.1 x.2)⟩
  map_one' := Subtype.ext (by decide)
  map_mul' x y := Subtype.ext (nrm_mul (show P6 from x.1) (show P6 from y.1))

theorem nrmHom_surjective : Function.Surjective nrmHom := fun y =>
  ⟨⟨(show (FFModel.altDn 6).Amb from (y : P6)), G6.mem_coreMod.2 y.2.1⟩,
    Subtype.ext (nrm_of_five y y.2.2)⟩

theorem ker_nrmHom :
    (FFModel.altDn 6).ker.subgroupOf (FFModel.altDn 6).sec = nrmHom.ker := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  show (show P6 from x.1) ∈ Subgroup.zpowers (G6.allOnes 6) ⊓ G6.coreMod 6 ↔ _
  rw [Subgroup.mem_inf, mem_zpowers_allOnes]
  constructor
  · rintro ⟨h, -⟩
    exact Subtype.ext ((nrm_eq_one_iff _).2 h)
  · intro h
    exact ⟨(nrm_eq_one_iff _).1 (congrArg Subtype.val h), x.2⟩

@[expose] noncomputable def modW4Equiv : (FFModel.altDn 6).Mod ≃* ↥W4 :=
  (QuotientGroup.quotientMulEquivOfEq ker_nrmHom).trans
    (QuotientGroup.quotientKerEquivOfSurjective nrmHom nrmHom_surjective)

theorem modW4Equiv_mk (m : ↥(FFModel.altDn 6).sec) :
    modW4Equiv (QuotientGroup.mk m) = nrmHom m := by
  rw [modW4Equiv, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem act4_injective : Function.Injective act4 := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have key : ∀ σ : Perm (Fin 6), (∀ x : P6, InW4 x → act4f σ x = x) → σ = 1 := by
    decide +kernel
  exact key σ fun x hx => congrArg Subtype.val (DFunLike.congr_fun hσ (⟨x, hx⟩ : ↥W4))

variable {G : Type} [Group G]

structure RawData4 (L V : Subgroup G) where
  hnorm : L ≤ Subgroup.normalizer (V : Set G)
  θ : ↥L →* ↥(alternatingGroup (Fin 6))
  ψ : ↥V ≃* ↥W4
  surj : Function.Surjective θ
  equiv : ∀ (l : ↥L) (v : ↥V),
    ψ (conjAct V ⟨l, hnorm l.2⟩ v) = act4 (θ l : Perm (Fin 6)) (ψ v)

open scoped IsMulCommutative in
theorem exists_rawData4 {L V : Subgroup G} [IsMulCommutative ↥V]
    (hL : L ≤ Subgroup.normalizer (V : Set G))
    (h : AlternatingNatural (V := ↥V) (autOn L V) ⊤ ⊥ 6) : Nonempty (RawData4 L V) := by
  obtain ⟨π, hπ⟩ := h
  have hinj := hπ.injective_of_faithful (altDn_faithful (by norm_num))
  let e : ↥(alternatingGroup (Fin 6)) ≃* ↥(autOn L V) := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  obtain ⟨E, hE⟩ := G64.RealizesVia.exists_modEquiv hπ
  refine ⟨{ hnorm := hL
            θ := e.symm.toMonoidHom.comp (autOnHom hL)
            ψ := E.trans modW4Equiv
            surj := e.symm.surjective.comp (autOnHom_surjective hL)
            equiv := fun l v => ?_ }⟩
  have he : ((π (e.symm (autOnHom hL l)) : ↥(autOn L V)) : MulAut ↥V) =
      conjAct V ⟨l, hL l.2⟩ := by
    have : π (e.symm (autOnHom hL l)) = autOnHom hL l := e.apply_symm_apply _
    rw [this, autOnHom_apply]
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (E v)
  have hact : (FFModel.altDn 6).act (e.symm (autOnHom hL l)) m.1 ∈ (FFModel.altDn 6).sec :=
    G6.permAct_mem_coreMod _ m.2
  have := hE (e.symm (autOnHom hL l)) v m hact hm.symm
  rw [he] at this
  show modW4Equiv (E (conjAct V ⟨l, hL l.2⟩ v)) =
    act4 ((e.symm (autOnHom hL l) : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6))
      (modW4Equiv (E v))
  rw [this, ← hm, modW4Equiv_mk, modW4Equiv_mk]
  apply Subtype.ext
  show nrm (G6.permAct 6 _ (show P6 from m.1)) = nrm (G6.permAct 6 _ (nrm (show P6 from m.1)))
  rw [nrm_permAct_nrm]

section Ext

variable {L V : Subgroup G} (R : RawData4 L V)

@[expose] noncomputable def alpha4 (g : ↥(Subgroup.normalizer (V : Set G))) : MulAut ↥W4 :=
  (R.ψ.symm.trans (conjAct V g)).trans R.ψ

theorem alpha4_apply (g : ↥(Subgroup.normalizer (V : Set G))) (x : ↥W4) :
    alpha4 R g x = R.ψ (conjAct V g (R.ψ.symm x)) := rfl

theorem alpha4_mul (g h : ↥(Subgroup.normalizer (V : Set G))) :
    alpha4 R (g * h) = alpha4 R g * alpha4 R h := by
  refine MulEquiv.ext fun x => ?_
  rw [MulAut.mul_apply, alpha4_apply, alpha4_apply, alpha4_apply, map_mul, MulAut.mul_apply,
    MulEquiv.symm_apply_apply]

theorem alpha4_L (l : ↥L) :
    alpha4 R ⟨l, R.hnorm l.2⟩ = act4 (R.θ l : Perm (Fin 6)) := by
  refine MulEquiv.ext fun x => ?_
  rw [alpha4_apply, R.equiv, MulEquiv.apply_symm_apply]

theorem exists_perm_alpha4 (g : ↥(Subgroup.normalizer (V : Set G)))
    (hgL : (g : G) ∈ Subgroup.normalizer (L : Set G)) :
    ∃ π : Perm (Fin 6), alpha4 R g = act4 π := by
  have key : ∀ (l l' : ↥L), (l' : G) = g * l * (g : G)⁻¹ → ∀ x,
      alpha4 R g (act4 (R.θ l : Perm (Fin 6)) x) =
        act4 (R.θ l' : Perm (Fin 6)) (alpha4 R g x) := by
    intro l l' hl' x
    rw [← alpha4_L, ← alpha4_L, ← MulAut.mul_apply, ← MulAut.mul_apply, ← alpha4_mul,
      ← alpha4_mul]
    congr 2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hl']
    group
  obtain ⟨π, hπ⟩ := exists_perm_of_normalizes_W4 (alpha4 R g) (fun σ hσ => by
      obtain ⟨l, hl⟩ := R.surj ⟨σ, hσ⟩
      let l' : ↥L := ⟨g * l * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp hgL l).mp l.2⟩
      refine ⟨R.θ l', (R.θ l').2, fun x => ?_⟩
      have := key l l' rfl x
      rwa [hl] at this)
  exact ⟨π, MulEquiv.ext hπ⟩

end Ext

section FrameGen

theorem exists_conj_frame {T L V : Subgroup G}
    (ρ0 : ↥(Subgroup.normalizer (V : Set G)) →* Perm (Fin 6))
    (θ : ↥L →* ↥(alternatingGroup (Fin 6))) (hsurj : Function.Surjective θ)
    (hnorm : L ≤ Subgroup.normalizer (V : Set G))
    (hρ0L : ∀ l : ↥L, ρ0 ⟨l, hnorm l.2⟩ = (θ l : Perm (Fin 6)))
    (hT : IsPGroup 2 T) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hsylL : IsSylowTwoOf (T ⊓ L) L) :
    ∃ π : Perm (Fin 6),
      (∀ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ T → InD6 (π * ρ0 g * π⁻¹)) ∧
      (∀ σ : Perm (Fin 6), InD6 σ → σ ∈ alternatingGroup (Fin 6) →
        ∃ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ T ∧ π * ρ0 g * π⁻¹ = σ) ∧
      ∀ σ : Perm (Fin 6),
        (∃ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ L ∧ π * ρ0 g * π⁻¹ = σ) ↔
          σ ∈ alternatingGroup (Fin 6) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Subgroup (Perm (Fin 6)) := (T.subgroupOf (Subgroup.normalizer (V : Set G))).map ρ0
  have hP : IsPGroup 2 P :=
    (hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTV).symm).map ρ0
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨π, hπ⟩ := MulAction.exists_smul_eq (Perm (Fin 6)) Q D6syl
  let ρ : ↥(Subgroup.normalizer (V : Set G)) →* Perm (Fin 6) :=
    (MulAut.conj π).toMonoidHom.comp ρ0
  have hρ : ∀ g, ρ g = π * ρ0 g * π⁻¹ := fun g => rfl
  have hTD : ∀ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ T → InD6 (ρ g) := by
    intro g hg
    have h1 : ρ0 g ∈ (Q : Subgroup (Perm (Fin 6))) := hPQ ⟨g, hg, rfl⟩
    have h2 : MulAut.conj π (ρ0 g) ∈ MulAut.conj π • (Q : Subgroup (Perm (Fin 6))) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ h1
    rw [← Sylow.coe_subgroup_smul, hπ] at h2
    have h3 : MulAut.conj π (ρ0 g) ∈ D6sub := h2
    exact h3
  have hρL : ∀ l : ↥L, ρ ⟨l, hnorm l.2⟩ = π * (θ l : Perm (Fin 6)) * π⁻¹ := by
    intro l
    rw [hρ, hρ0L]
  have hDA : ∀ σ : Perm (Fin 6), InD6 σ → σ ∈ alternatingGroup (Fin 6) →
      ∃ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ T ∧ ρ g = σ := by
    let φ : ↥((T ⊓ L).subgroupOf L) →* Perm (Fin 6) :=
      (MulAut.conj π).toMonoidHom.comp
        ((alternatingGroup (Fin 6)).subtype.comp (θ.comp ((T ⊓ L).subgroupOf L).subtype))
    have hφ2 : IsPGroup 2 φ.range := by
      have h1 : IsPGroup 2 ↥((T ⊓ L).subgroupOf L) :=
        hsylL.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
      have h1top : IsPGroup 2 (⊤ : Subgroup ↥((T ⊓ L).subgroupOf L)) :=
        h1.of_equiv Subgroup.topEquiv.symm
      have := h1top.map φ
      rwa [← MonoidHom.range_eq_map] at this
    have hcard8 : Nat.card φ.range = 8 := by
      let θT : ↥((T ⊓ L).subgroupOf L) →* ↥(alternatingGroup (Fin 6)) :=
        θ.comp ((T ⊓ L).subgroupOf L).subtype
      have hrange : θT.range = ((T ⊓ L).subgroupOf L).map θ := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      have hidx : θT.range.index ∣ ((T ⊓ L).subgroupOf L).index := by
        rw [hrange]
        exact Subgroup.index_map_dvd _ hsurj
      have hodd : ¬ 2 ∣ θT.range.index := fun h => hsylL.2.2 (h.trans hidx)
      have h2θ : IsPGroup 2 θT.range := by
        have h1 : IsPGroup 2 ↥((T ⊓ L).subgroupOf L) :=
          hsylL.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
        have h1top : IsPGroup 2 (⊤ : Subgroup ↥((T ⊓ L).subgroupOf L)) :=
          h1.of_equiv Subgroup.topEquiv.symm
        have := h1top.map θT
        rwa [← MonoidHom.range_eq_map] at this
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 h2θ
      have hA6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        decide
      have hmul := Subgroup.card_mul_index θT.range
      rw [hk, hA6] at hmul
      have hk3 : k = 3 := by
        have hk8 : k ≤ 8 := by
          by_contra hk8
          have : 2 ^ 9 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
          rcases Nat.eq_zero_or_pos θT.range.index with h0 | hpos
          · rw [h0] at hmul; omega
          · nlinarith
        interval_cases k <;> omega
      have hφeq : φ.range = θT.range.map
          ((MulAut.conj π).toMonoidHom.comp (alternatingGroup (Fin 6)).subtype) := by
        rw [MonoidHom.range_eq_map, MonoidHom.range_eq_map, Subgroup.map_map]
        rfl
      rw [hφeq, Subgroup.card_map_of_injective, hk, hk3]
      · norm_num
      · exact ((MulAut.conj π).injective.comp Subtype.val_injective)
    have hle : ∀ σ ∈ φ.range, InD6 σ ∧ σ ∈ alternatingGroup (Fin 6) := by
      rintro _ ⟨⟨t, ht⟩, rfl⟩
      rw [Subgroup.mem_subgroupOf] at ht
      have hD := hTD ⟨t, hTV ht.1⟩ ht.1
      have hgeq : (⟨t, hTV ht.1⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          ⟨(⟨t, ht.2⟩ : ↥L), hnorm ht.2⟩ := rfl
      rw [hgeq, hρL] at hD
      refine ⟨hD, inDA_of_conj (θ ⟨t, ht.2⟩).2⟩
    let DA : Finset (Perm (Fin 6)) :=
      Finset.univ.filter fun σ : Perm (Fin 6) => InD6 σ ∧ Equiv.Perm.sign σ = 1
    have hDAcard : DA.card = 8 := card_DA
    have hsub : (φ.range : Set (Perm (Fin 6))).toFinset ⊆ DA := by
      intro σ hσ
      simp only [Set.mem_toFinset, SetLike.mem_coe] at hσ
      simp only [DA, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(hle σ hσ).1, Equiv.Perm.mem_alternatingGroup.1 (hle σ hσ).2⟩
    have hcardR : (φ.range : Set (Perm (Fin 6))).toFinset.card = 8 := by
      rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
      exact hcard8
    have heq : (φ.range : Set (Perm (Fin 6))).toFinset = DA :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcardR, hDAcard])
    intro σ hσD hσA
    have hmem : σ ∈ φ.range := by
      have : σ ∈ DA := by
        simp only [DA, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hσD, Equiv.Perm.mem_alternatingGroup.1 hσA⟩
      rw [← heq, Set.mem_toFinset] at this
      exact this
    obtain ⟨⟨t, ht⟩, hφt⟩ := hmem
    rw [Subgroup.mem_subgroupOf] at ht
    refine ⟨⟨t, hTV ht.1⟩, ht.1, ?_⟩
    have hgeq : (⟨t, hTV ht.1⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨(⟨t, ht.2⟩ : ↥L), hnorm ht.2⟩ := rfl
    rw [hgeq, hρL, ← hφt]
    rfl
  refine ⟨π, hTD, hDA, fun σ => ?_⟩
  constructor
  · rintro ⟨g, hgL, rfl⟩
    have : g = ⟨(⟨g, hgL⟩ : ↥L), hnorm hgL⟩ := rfl
    rw [this, ← hρ, hρL]
    exact inDA_of_conj (θ ⟨g, hgL⟩).2
  · intro hσ
    have hσ' : π⁻¹ * σ * π ∈ alternatingGroup (Fin 6) := by
      have := inDA_of_conj (π := π⁻¹) hσ
      rwa [inv_inv] at this
    obtain ⟨l, hl⟩ := hsurj ⟨π⁻¹ * σ * π, hσ'⟩
    refine ⟨⟨l, hnorm l.2⟩, l.2, ?_⟩
    rw [← hρ, hρL, hl]
    group

end FrameGen

section Rho

variable {L V : Subgroup G} (R : RawData4 L V)
  (hNL : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G))

@[expose] noncomputable def rho4 : ↥(Subgroup.normalizer (V : Set G)) →* Perm (Fin 6) where
  toFun g := Classical.choose (exists_perm_alpha4 R g (hNL g.2))
  map_one' := by
    apply act4_injective
    rw [← Classical.choose_spec (exists_perm_alpha4 R 1
      (hNL (1 : ↥(Subgroup.normalizer (V : Set G))).2)), map_one]
    refine MulEquiv.ext fun x => ?_
    rw [alpha4_apply, map_one, MulAut.one_apply, MulEquiv.apply_symm_apply, MulAut.one_apply]
  map_mul' g h := by
    apply act4_injective
    rw [← Classical.choose_spec (exists_perm_alpha4 R (g * h) (hNL (g * h).2)), map_mul,
      ← Classical.choose_spec (exists_perm_alpha4 R g (hNL g.2)),
      ← Classical.choose_spec (exists_perm_alpha4 R h (hNL h.2)), alpha4_mul]

theorem act4_rho4 (g : ↥(Subgroup.normalizer (V : Set G))) :
    act4 (rho4 R hNL g) = alpha4 R g :=
  (Classical.choose_spec (exists_perm_alpha4 R g (hNL g.2))).symm

theorem rho4_L (l : ↥L) : rho4 R hNL ⟨l, R.hnorm l.2⟩ = (R.θ l : Perm (Fin 6)) := by
  apply act4_injective
  rw [act4_rho4, alpha4_L]

theorem psi_conjAct_rho4 (g : ↥(Subgroup.normalizer (V : Set G))) (v : ↥V) :
    R.ψ (conjAct V g v) = act4 (rho4 R hNL g) (R.ψ v) := by
  rw [act4_rho4, alpha4_apply, MulEquiv.symm_apply_apply]

end Rho

theorem exists_frame4 {T L V : Subgroup G} (R : RawData4 L V)
    (hNL : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hT : IsPGroup 2 T) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hsylL : IsSylowTwoOf (T ⊓ L) L) : Nonempty (Frame4 T L V) := by
  obtain ⟨π, hTD, hDA, himg⟩ :=
    exists_conj_frame (rho4 R hNL) R.θ R.surj R.hnorm (rho4_L R hNL) hT hTV hsylL
  refine ⟨{ L_le := R.hnorm
            T_le := hTV
            ψ := R.ψ.trans (act4 π)
            ρ := (MulAut.conj π).toMonoidHom.comp (rho4 R hNL)
            equiv := fun g v => ?_
            image_L := himg
            T_D := hTD
            DA_T := hDA }⟩
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, psi_conjAct_rho4 R hNL,
    ← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
  congr 2
  show π * rho4 R hNL g = π * rho4 R hNL g * π⁻¹ * π
  group

open scoped IsMulCommutative in
theorem exists_setting4 (h1332 : Stmt13_3_2) (h13316 : Stmt13_3_16) [Finite G]
    {T L V : Subgroup G} (h : QTH13 G T L) (hA6 : A6CentralQuotient L)
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V)
    (hZV : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) : Nonempty (Setting4 G T L V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨hTN, hmax, hMmax, huniq⟩, ⟨-, hall⟩, -⟩ := h1332 G T L h L h.faithful
  have uniqueM : IsUniqueM (L ⊔ T) (Subgroup.normalizer (L : Set G)) :=
    ⟨⟨hMmax, sup_le Subgroup.le_normalizer hTN⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩
  obtain ⟨hVT, hTV, hfsu, hab, hmod⟩ := hall V hV
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hV.2.2.1
  have hnat : AlternatingNatural (V := ↥V) (autOn L V) ⊤ ⊥ 6 := by
    rcases hmod with ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨-, hc2, -⟩ | ⟨hl, -, -⟩ | ⟨hu, -, -⟩
    · exfalso
      obtain ⟨e⟩ := nonempty_mulEquiv_of_realizes (altDn_faithful (by norm_num)) h5
      obtain ⟨φ, hφ⟩ := exists_surjective_autOn hLV
      exact false_of_surjective_alt5 hA6 (e.toMonoidHom.comp φ) (e.surjective.comp hφ)
    · exact h6
    · exfalso
      rw [hZV, Subgroup.card_bot] at hc2
      exact absurd hc2 (by norm_num)
    · exact (false_of_psl32_of_a6CentralQuotient hA6 hl).elim
    · exact (h13316 G T L h hu).elim
  obtain ⟨R⟩ := exists_rawData4 hLV hnat
  have hcard : Nat.card V = 16 := by
    rw [Nat.card_congr R.ψ.toEquiv]
    have : Fintype.card {x : P6 // InW4 x} = 16 := by decide +kernel
    rw [← this, ← Nat.card_eq_fintype_card]
    rfl
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 4) (by rw [hcard]; norm_num)
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  have hNL : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
      (⟨V, hV.2.1, hV2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (V : Set G)))
    have := uniqueM.2 M' ⟨hM', hLTV.trans hM'le⟩
    exact this ▸ hM'le
  have hsylLT : IsSylowTwoOf T (L ⊔ T) := A5.isSylowTwoOf_of_le h.sylow le_sup_right
  have hsylL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hsylLT le_sup_left (sup_le Subgroup.le_normalizer hTN)
  obtain ⟨F⟩ := exists_frame4 R hNL h.sylow.1 hTV hsylL
  exact ⟨{
    h13 := h
    irr := hV
    zv := hZV
    T_le_NL := hTN
    maximal := hmax
    uniqueM := uniqueM
    V_le_T := hVT
    fsu := hfsu
    a6 := nonempty_mulEquiv_of_realizes (altDn_faithful (by norm_num)) hnat
    centralQuot := hA6
    frame := F }⟩

end CFSG.Quasithin.H13.A6
