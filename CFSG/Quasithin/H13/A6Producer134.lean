module

public import CFSG.Quasithin.H13.A6Setting134
public import CFSG.Quasithin.H13.A6Realize
public import CFSG.Quasithin.H13.A5Setting
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

theorem InD6.blocks : ∀ σ : Perm (Fin 6), InD6 σ → ∀ i j : Fin 6, (i : ℕ) / 2 = (j : ℕ) / 2 →
    (σ i : ℕ) / 2 = (σ j : ℕ) / 2 := by
  decide +kernel

theorem InD6.inv : ∀ σ : Perm (Fin 6), InD6 σ → InD6 σ⁻¹ := by
  decide +kernel

@[expose] def D6sub : Subgroup (Perm (Fin 6)) where
  carrier := {σ | InD6 σ}
  one_mem' := by decide
  mul_mem' := fun {a b} ha hb => by
    have ha' := InD6.blocks a ha
    obtain ⟨hb4, hb5, hb01⟩ := hb
    obtain ⟨ha4, -, -⟩ := ha
    refine ⟨?_, ?_, ?_⟩
    · show ((a (b 4)) : ℕ) / 2 = 2
      rw [ha' (b 4) 4 (by rw [hb4]; rfl), ha4]
    · show ((a (b 5)) : ℕ) / 2 = 2
      rw [ha' (b 5) 4 (by rw [hb5]; rfl), ha4]
    · show ((a (b 0)) : ℕ) / 2 = ((a (b 1)) : ℕ) / 2
      exact ha' (b 0) (b 1) hb01
  inv_mem' := fun {a} ha => InD6.inv a ha

theorem mem_D6sub {σ : Perm (Fin 6)} : σ ∈ D6sub ↔ InD6 σ := Iff.rfl

theorem card_D6sub : Nat.card D6sub = 16 := by
  have : Fintype.card {σ : Perm (Fin 6) // InD6 σ} = 16 := by decide +kernel
  rw [← this, ← Nat.card_eq_fintype_card]
  rfl

@[expose] noncomputable def D6syl : Sylow 2 (Perm (Fin 6)) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  Sylow.ofCard D6sub (by
    rw [card_D6sub, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    have h : Nat.factorial 6 = 2 ^ 4 * 45 := by decide
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.Prime.factorization_pow Nat.prime_two]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num)]; rfl)

theorem card_DA :
    (Finset.univ.filter fun σ : Perm (Fin 6) => InD6 σ ∧ Equiv.Perm.sign σ = 1).card = 8 := by
  decide +kernel

variable {G : Type} [Group G]

structure RawData6 (L V : Subgroup G) where
  hnorm : L ≤ Subgroup.normalizer (V : Set G)
  θ : ↥L →* ↥(alternatingGroup (Fin 6))
  ψ : ↥V ≃* ↥(G6.coreMod 6)
  surj : Function.Surjective θ
  equiv : ∀ (l : ↥L) (v : ↥V),
    ψ (conjAct V ⟨l, hnorm l.2⟩ v) = G6.coreAct 6 (θ l : Perm (Fin 6)) (ψ v)

open scoped IsMulCommutative in
theorem exists_rawData6 {L V : Subgroup G} [IsMulCommutative ↥V]
    (hL : L ≤ Subgroup.normalizer (V : Set G))
    (h : FFModel.Realizes (V := ↥V) (altCoreModel 6) (autOn L V) ⊤ ⊥) :
    Nonempty (RawData6 L V) := by
  obtain ⟨π, hπ⟩ := h
  have hinj := hπ.injective_of_faithful (altCoreModel_faithful (by norm_num))
  let e : ↥(alternatingGroup (Fin 6)) ≃* ↥(autOn L V) := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  obtain ⟨E, hE⟩ := G64.RealizesVia.exists_secEquiv rfl hπ
  refine ⟨{ hnorm := hL
            θ := e.symm.toMonoidHom.comp (autOnHom hL)
            ψ := E
            surj := e.symm.surjective.comp (autOnHom_surjective hL)
            equiv := fun l v => ?_ }⟩
  apply Subtype.ext
  have he : ((π (e.symm (autOnHom hL l)) : ↥(autOn L V)) : MulAut ↥V) = conjAct V ⟨l, hL l.2⟩ := by
    have : π (e.symm (autOnHom hL l)) = autOnHom hL l := e.apply_symm_apply _
    rw [this, autOnHom_apply]
  have := hE (e.symm (autOnHom hL l)) v
  rw [he] at this
  rw [G6.coreAct_coe]
  exact this

section Ext

variable {L V : Subgroup G} (R : RawData6 L V)

@[expose] noncomputable def alphaOf (g : ↥(Subgroup.normalizer (V : Set G))) :
    MulAut ↥(G6.coreMod 6) :=
  (R.ψ.symm.trans (conjAct V g)).trans R.ψ

theorem alphaOf_apply (g : ↥(Subgroup.normalizer (V : Set G))) (x : ↥(G6.coreMod 6)) :
    alphaOf R g x = R.ψ (conjAct V g (R.ψ.symm x)) := rfl

theorem alphaOf_mul (g h : ↥(Subgroup.normalizer (V : Set G))) :
    alphaOf R (g * h) = alphaOf R g * alphaOf R h := by
  refine MulEquiv.ext fun x => ?_
  rw [MulAut.mul_apply, alphaOf_apply, alphaOf_apply, alphaOf_apply, map_mul, MulAut.mul_apply,
    MulEquiv.symm_apply_apply]

theorem alphaOf_L (l : ↥L) :
    alphaOf R ⟨l, R.hnorm l.2⟩ = G6.coreAct 6 (R.θ l : Perm (Fin 6)) := by
  refine MulEquiv.ext fun x => ?_
  rw [alphaOf_apply, R.equiv, MulEquiv.apply_symm_apply]

theorem exists_perm_alphaOf (g : ↥(Subgroup.normalizer (V : Set G)))
    (hgL : (g : G) ∈ Subgroup.normalizer (L : Set G)) :
    ∃ π : Perm (Fin 6), alphaOf R g = G6.coreAct 6 π := by
  have hconj : ∀ l : ↥L, ∃ l' : ↥L, (l' : G) = g * l * (g : G)⁻¹ := fun l =>
    ⟨⟨g * l * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp hgL l).mp l.2⟩, rfl⟩
  have key : ∀ (l l' : ↥L), (l' : G) = g * l * (g : G)⁻¹ → ∀ x,
      alphaOf R g (G6.coreAct 6 (R.θ l : Perm (Fin 6)) x) =
        G6.coreAct 6 (R.θ l' : Perm (Fin 6)) (alphaOf R g x) := by
    intro l l' hl' x
    rw [← alphaOf_L, ← alphaOf_L, ← MulAut.mul_apply, ← MulAut.mul_apply, ← alphaOf_mul,
      ← alphaOf_mul]
    congr 2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hl']
    group
  obtain ⟨π, hπ⟩ := exists_perm_of_normalizes_core (alphaOf R g) (fun σ hσ => by
      obtain ⟨l, hl⟩ := R.surj ⟨σ, hσ⟩
      obtain ⟨l', hl'⟩ := hconj l
      refine ⟨R.θ l', (R.θ l').2, fun x => ?_⟩
      have := key l l' hl' x
      rwa [hl] at this)
    (fun τ hτ => by
      obtain ⟨l', hl'⟩ := R.surj ⟨τ, hτ⟩
      let l : ↥L := ⟨(g : G)⁻¹ * l' * g, by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgL) l').mp l'.2
        simpa using this⟩
      refine ⟨R.θ l, (R.θ l).2, fun x => ?_⟩
      have := key l l' (by simp [l]; group) x
      rwa [hl'] at this)
  exact ⟨π, MulEquiv.ext hπ⟩

end Ext

theorem coreAct_injective : Function.Injective (G6.coreAct 6) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  refine G64.symCore_faithful (n := 6) (by norm_num) σ fun (m : G6.PermMod 6) hm => ?_
  have := DFunLike.congr_fun hσ ⟨m, hm⟩
  have h2 := congrArg Subtype.val this
  rw [G6.coreAct_coe] at h2
  show G6.permAct 6 σ m * m⁻¹ ∈ (⊥ : Subgroup (G6.PermMod 6))
  rw [Subgroup.mem_bot, h2]
  exact mul_inv_cancel m

section Rho

variable {L V : Subgroup G} (R : RawData6 L V)
  (hNL : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G))

@[expose] noncomputable def rho0 : ↥(Subgroup.normalizer (V : Set G)) →* Perm (Fin 6) where
  toFun g := Classical.choose (exists_perm_alphaOf R g (hNL g.2))
  map_one' := by
    apply coreAct_injective
    rw [← Classical.choose_spec (exists_perm_alphaOf R 1
      (hNL (1 : ↥(Subgroup.normalizer (V : Set G))).2)), map_one]
    refine MulEquiv.ext fun x => ?_
    rw [alphaOf_apply, map_one, MulAut.one_apply, MulEquiv.apply_symm_apply, MulAut.one_apply]
  map_mul' g h := by
    apply coreAct_injective
    rw [← Classical.choose_spec (exists_perm_alphaOf R (g * h) (hNL (g * h).2)), map_mul,
      ← Classical.choose_spec (exists_perm_alphaOf R g (hNL g.2)),
      ← Classical.choose_spec (exists_perm_alphaOf R h (hNL h.2)), alphaOf_mul]

theorem coreAct_rho0 (g : ↥(Subgroup.normalizer (V : Set G))) :
    G6.coreAct 6 (rho0 R hNL g) = alphaOf R g :=
  (Classical.choose_spec (exists_perm_alphaOf R g (hNL g.2))).symm

theorem rho0_L (l : ↥L) : rho0 R hNL ⟨l, R.hnorm l.2⟩ = (R.θ l : Perm (Fin 6)) := by
  apply coreAct_injective
  rw [coreAct_rho0, alphaOf_L]

theorem psi_conjAct_rho0 (g : ↥(Subgroup.normalizer (V : Set G))) (v : ↥V) :
    R.ψ (conjAct V g v) = G6.coreAct 6 (rho0 R hNL g) (R.ψ v) := by
  rw [coreAct_rho0, alphaOf_apply, MulEquiv.symm_apply_apply]

end Rho

section FrameExist

theorem inDA_of_conj {π σ : Perm (Fin 6)} (h : σ ∈ alternatingGroup (Fin 6)) :
    π * σ * π⁻¹ ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup] at h ⊢
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, h, Equiv.Perm.sign_inv]
  simp

theorem exists_frame5 {T L V : Subgroup G} (R : RawData6 L V)
    (hNL : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hT : IsPGroup 2 T) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hsylL : IsSylowTwoOf (T ⊓ L) L) : Nonempty (Frame5 T L V) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ0 := rho0 R hNL with hρ0
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
  have hρL : ∀ l : ↥L, ρ ⟨l, R.hnorm l.2⟩ = π * (R.θ l : Perm (Fin 6)) * π⁻¹ := by
    intro l
    rw [hρ, rho0_L]
  have hDA : ∀ σ : Perm (Fin 6), InD6 σ → σ ∈ alternatingGroup (Fin 6) →
      ∃ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ T ∧ ρ g = σ := by
    let φ : ↥((T ⊓ L).subgroupOf L) →* Perm (Fin 6) :=
      (MulAut.conj π).toMonoidHom.comp
        ((alternatingGroup (Fin 6)).subtype.comp (R.θ.comp ((T ⊓ L).subgroupOf L).subtype))
    have hφ2 : IsPGroup 2 φ.range := by
      have h1 : IsPGroup 2 ↥((T ⊓ L).subgroupOf L) :=
        hsylL.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
      have h1top : IsPGroup 2 (⊤ : Subgroup ↥((T ⊓ L).subgroupOf L)) :=
        h1.of_equiv Subgroup.topEquiv.symm
      have := h1top.map φ
      rwa [← MonoidHom.range_eq_map] at this
    have hcard8 : Nat.card φ.range = 8 := by
      let θT : ↥((T ⊓ L).subgroupOf L) →* ↥(alternatingGroup (Fin 6)) :=
        R.θ.comp ((T ⊓ L).subgroupOf L).subtype
      have hrange : θT.range = ((T ⊓ L).subgroupOf L).map R.θ := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      have hidx : θT.range.index ∣ ((T ⊓ L).subgroupOf L).index := by
        rw [hrange]
        exact Subgroup.index_map_dvd _ R.surj
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
          ⟨(⟨t, ht.2⟩ : ↥L), R.hnorm ht.2⟩ := rfl
      rw [hgeq, hρL] at hD
      refine ⟨hD, inDA_of_conj (R.θ ⟨t, ht.2⟩).2⟩
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
        ⟨(⟨t, ht.2⟩ : ↥L), R.hnorm ht.2⟩ := rfl
    rw [hgeq, hρL, ← hφt]
    rfl
  refine ⟨{ L_le := R.hnorm
            T_le := hTV
            ψ := R.ψ.trans (G6.coreAct 6 π)
            ρ := ρ
            equiv := fun g v => ?_
            image_L := fun σ => ?_
            T_D := hTD
            DA_T := hDA }⟩
  · rw [MulEquiv.trans_apply, MulEquiv.trans_apply, psi_conjAct_rho0 R hNL, hρ,
      ← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
    congr 2
    rw [hρ0]
    group
  · constructor
    · rintro ⟨g, hgL, rfl⟩
      have : g = ⟨(⟨g, hgL⟩ : ↥L), R.hnorm hgL⟩ := rfl
      rw [this, hρL]
      exact inDA_of_conj (R.θ ⟨g, hgL⟩).2
    · intro hσ
      have hσ' : π⁻¹ * σ * π ∈ alternatingGroup (Fin 6) := by
        have := inDA_of_conj (π := π⁻¹) hσ
        rwa [inv_inv] at this
      obtain ⟨l, hl⟩ := R.surj ⟨π⁻¹ * σ * π, hσ'⟩
      refine ⟨⟨l, R.hnorm l.2⟩, l.2, ?_⟩
      rw [hρL, hl]
      group

end FrameExist

open scoped IsMulCommutative in
theorem exists_setting134 (h1332 : Stmt13_3_2) [Finite G] {T L V : Subgroup G}
    (h : QTH13 G T L) (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V)
    (hZV : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) : Nonempty (Setting134 G T L V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨hTN, hmax, hMmax, huniq⟩, ⟨-, hall⟩, -⟩ := h1332 G T L h L h.faithful
  have uniqueM : IsUniqueM (L ⊔ T) (Subgroup.normalizer (L : Set G)) :=
    ⟨⟨hMmax, sup_le Subgroup.le_normalizer hTN⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩
  obtain ⟨hVT, hTV, hfsu, hab, hmod⟩ := hall V hV
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hV.2.2.1
  have hc : Nat.card V = 2 ^ 5 ∧
      FFModel.Realizes (V := ↥V) (altCoreModel 6) (autOn L V) ⊤ ⊥ := by
    rcases hmod with h1 | h2 | h3 | h4 | h5
    · exact absurd h1.2 hZV
    · exact absurd h2.2 hZV
    · exact ⟨h3.1, h3.2.2⟩
    · exact absurd h4.2.2 hZV
    · exact absurd h5.2.2 hZV
  obtain ⟨R⟩ := exists_rawData6 hLV hc.2
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 5) hc.1
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  have hNL : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
      (⟨V, hV.2.1, hV2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (V : Set G)))
    have := uniqueM.2 M' ⟨hM', hLTV.trans hM'le⟩
    exact this ▸ hM'le
  have hsylLT : IsSylowTwoOf T (L ⊔ T) := A5.isSylowTwoOf_of_le h.sylow le_sup_right
  have hsylL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hsylLT le_sup_left (sup_le Subgroup.le_normalizer hTN)
  obtain ⟨F⟩ := exists_frame5 R hNL h.sylow.1 hTV hsylL
  exact ⟨{
    h13 := h
    irr := hV
    zv := hZV
    T_le_NL := hTN
    maximal := hmax
    uniqueM := uniqueM
    V_le_T := hVT
    fsu := hfsu
    frame := F }⟩

end CFSG.Quasithin.H13.A6
