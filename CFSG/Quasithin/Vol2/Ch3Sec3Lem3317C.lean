module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3317B
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316D
public import CFSG.Quasithin.Background.C126RFCases
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3317CPack

public section

namespace CFSG.Quasithin.H13.L3317

open Equiv Equiv.Perm

section Alt

theorem card_filter_stabFS : (Finset.univ.filter fun σ : Perm (Fin 7) =>
    sign σ = 1 ∧ ((σ 5 = 5 ∧ σ 6 = 6) ∨ (σ 5 = 6 ∧ σ 6 = 5))).card = 120 :=
  L3317Pack.card_stabFS_pack

theorem nat_card_stabFS : Nat.card (A7.stabA7 A7.vecFS) = 120 := by
  rw [← card_filter_stabFS, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr ⟨fun x => ⟨(x : alternatingGroup (Fin 7)), ?_⟩,
    fun x => ⟨⟨(x : Perm (Fin 7)), mem_alternatingGroup.2 (x.2).1⟩, ?_⟩,
    fun x => rfl, fun x => rfl⟩
  · exact ⟨mem_alternatingGroup.1 (x : alternatingGroup (Fin 7)).2,
      (A7.permAct7_vecFS_iff _).1 x.2⟩
  · exact (A7.permAct7_vecFS_iff _).2 (x.2).2

theorem stabFS_le_normalizer_altFive :
    A7.stabA7 A7.vecFS ≤ Subgroup.normalizer (A7.altFive : Set (alternatingGroup (Fin 7))) := by
  intro σ hσ
  have h56 := (A7.permAct7_vecFS_iff _).1 hσ
  rw [Subgroup.mem_normalizer_iff]
  intro π
  have key : ∀ (τ : alternatingGroup (Fin 7)),
      ((τ : Perm (Fin 7)) 5 = 5 ∧ (τ : Perm (Fin 7)) 6 = 6) ∨
        ((τ : Perm (Fin 7)) 5 = 6 ∧ (τ : Perm (Fin 7)) 6 = 5) → ∀ ρ : alternatingGroup (Fin 7),
      ρ ∈ A7.altFive → τ * ρ * τ⁻¹ ∈ A7.altFive := by
    intro τ hτ ρ hρ
    rw [A7.mem_altFive] at hρ ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply]
    rcases hτ with ⟨h5, h6⟩ | ⟨h5, h6⟩
    · have h5' : (τ : Perm (Fin 7))⁻¹ 5 = 5 := by rw [Perm.inv_eq_iff_eq, h5]
      have h6' : (τ : Perm (Fin 7))⁻¹ 6 = 6 := by rw [Perm.inv_eq_iff_eq, h6]
      rw [h5', h6', hρ.1, hρ.2, h5, h6]
      exact ⟨rfl, rfl⟩
    · have h5' : (τ : Perm (Fin 7))⁻¹ 5 = 6 := by rw [Perm.inv_eq_iff_eq, h6]
      have h6' : (τ : Perm (Fin 7))⁻¹ 6 = 5 := by rw [Perm.inv_eq_iff_eq, h5]
      rw [h5', h6', hρ.1, hρ.2, h5, h6]
      exact ⟨rfl, rfl⟩
  constructor
  · exact key σ h56 π
  · intro hπ
    have hσ' : ((σ⁻¹ : alternatingGroup (Fin 7)) : Perm (Fin 7)) 5 = 5 ∧
        ((σ⁻¹ : alternatingGroup (Fin 7)) : Perm (Fin 7)) 6 = 6 ∨
        ((σ⁻¹ : alternatingGroup (Fin 7)) : Perm (Fin 7)) 5 = 6 ∧
        ((σ⁻¹ : alternatingGroup (Fin 7)) : Perm (Fin 7)) 6 = 5 := by
      simp only [Subgroup.coe_inv]
      rcases h56 with ⟨h5, h6⟩ | ⟨h5, h6⟩
      · left
        exact ⟨by rw [Perm.inv_eq_iff_eq, h5], by rw [Perm.inv_eq_iff_eq, h6]⟩
      · right
        exact ⟨by rw [Perm.inv_eq_iff_eq, h6], by rw [Perm.inv_eq_iff_eq, h5]⟩
    have := key σ⁻¹ hσ' _ hπ
    simpa [mul_assoc] using this

@[expose] def cyc012 : Perm (Fin 7) := swap 0 2 * swap 0 1

@[expose] def cyc01234 : Perm (Fin 7) := swap 0 4 * swap 0 3 * swap 0 2 * swap 0 1

@[expose] def CentFiveBad (σ : Perm (Fin 7)) : Prop :=
  sign σ = 1 ∧ σ * cyc012 = cyc012 * σ ∧ σ * cyc01234 = cyc01234 * σ ∧ σ ≠ 1

instance : DecidablePred CentFiveBad := fun σ => by
  unfold CentFiveBad
  infer_instance

theorem card_filter_centFiveBad : (Finset.univ.filter CentFiveBad).card = 0 :=
  Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun σ _ ⟨hs, h1, h2, hne⟩ =>
    hne (L3317Pack.eq_one_of_commute_pack cyc012 cyc01234 L3317Pack.enc_c012
      L3317Pack.enc_c01234 σ hs h1 h2))

theorem cyc012_mem : cyc012 ∈ alternatingGroup (Fin 7) := by
  rw [mem_alternatingGroup]
  decide

theorem cyc01234_mem : cyc01234 ∈ alternatingGroup (Fin 7) := by
  rw [mem_alternatingGroup]
  decide

theorem cyc012_mem_altFive : (⟨cyc012, cyc012_mem⟩ : alternatingGroup (Fin 7)) ∈ A7.altFive := by
  rw [A7.mem_altFive]
  decide

theorem cyc01234_mem_altFive :
    (⟨cyc01234, cyc01234_mem⟩ : alternatingGroup (Fin 7)) ∈ A7.altFive := by
  rw [A7.mem_altFive]
  decide

theorem eq_one_of_commute_altFive {σ : alternatingGroup (Fin 7)}
    (h : ∀ ρ ∈ A7.altFive, σ * ρ = ρ * σ) : σ = 1 := by
  by_contra hne
  have hbad : CentFiveBad (σ : Perm (Fin 7)) := by
    refine ⟨mem_alternatingGroup.1 σ.2, ?_, ?_, fun h1 => hne (Subtype.ext h1)⟩
    · exact congrArg Subtype.val (h _ cyc012_mem_altFive)
    · exact congrArg Subtype.val (h _ cyc01234_mem_altFive)
  have hmem : (σ : Perm (Fin 7)) ∈ Finset.univ.filter CentFiveBad :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hbad⟩
  rw [Finset.card_eq_zero.1 card_filter_centFiveBad] at hmem
  exact Finset.notMem_empty _ hmem

end Alt


section Sylow

theorem exists_card_eight_le_stabFS : ∃ Q : Subgroup (alternatingGroup (Fin 7)),
    Q ≤ A7.stabA7 A7.vecFS ∧ Nat.card Q = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥(A7.stabA7 A7.vecFS)))
  have hP := P.card_eq_multiplicity
  rw [nat_card_stabFS] at hP
  have h120 : (120 : ℕ).factorization 2 = 3 := by
    rw [show (120 : ℕ) = 2 ^ 3 * 15 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  refine ⟨(P : Subgroup ↥(A7.stabA7 A7.vecFS)).map (A7.stabA7 A7.vecFS).subtype,
    Subgroup.map_subtype_le _, ?_⟩
  rw [Subgroup.card_map_of_injective (A7.stabA7 A7.vecFS).subtype_injective, hP, h120]
  norm_num

theorem exists_conj_eq_of_card_eight {X Y : Subgroup (alternatingGroup (Fin 7))}
    (hX : Nat.card X = 8) (hY : Nat.card Y = 8) :
    ∃ g : alternatingGroup (Fin 7), X.map (MulAut.conj g).toMonoidHom = Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h8 : ∀ Z : Subgroup (alternatingGroup (Fin 7)), Nat.card Z = 8 →
      Nat.card Z = 2 ^ (Nat.card (alternatingGroup (Fin 7))).factorization 2 := by
    intro Z hZ
    rw [hZ, CFSG.GH74.SmallRanks.factorization_two_card_alt7]
    norm_num
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7))
    (Sylow.ofCard X (h8 X hX)) (Sylow.ofCard Y (h8 Y hY))
  refine ⟨g, ?_⟩
  have := congrArg (fun P : Sylow 2 (alternatingGroup (Fin 7)) => P.toSubgroup) hg
  simp only [Sylow.coe_subgroup_smul, Sylow.coe_ofCard] at this
  rw [← this]
  rfl

end Sylow


section Action

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique
open scoped IsMulCommutative

theorem card_autOn_eq_card_map (h : Hyp331 G T M L D)
    (e : ↥(autOn L (vPlus L T)) ≃* alternatingGroup (Fin 7)) (hML : mPlus L T = L)
    {X : Subgroup G} (hXL : X ≤ L) :
    Nat.card ↥(autOn X ⁅vPlus L T, L⁆) =
      Nat.card ↥((X.subgroupOf L).map (actA7 (le_normalizer_vPlus h) e)) := by
  have hLV := le_normalizer_vPlus h
  have hXW : X ≤ Subgroup.normalizer ((⁅vPlus L T, L⁆ : Subgroup G) : Set G) :=
    hXL.trans (le_normalizer_commV h)
  set f₁ := (actA7 hLV e).comp (Subgroup.inclusion hXL) with hf₁
  set f₂ := actL X ⁅vPlus L T, L⁆ hXW with hf₂
  have hker : f₁.ker = f₂.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hf₂, actL_eq_one_iff, hf₁, MonoidHom.comp_apply,
      ← MonoidHom.mem_ker, actA7_ker, Subgroup.mem_subgroupOf]
    have hC := Subgroup.ext_iff.1 (inf_centralizer_commV h hML) x
    exact ⟨fun hx => (hC.2 ⟨hXL x.2, hx⟩).2, fun hx => (hC.1 ⟨hXL x.2, hx⟩).2⟩
  have h1 := Subgroup.index_ker f₁
  have h2 := Subgroup.index_ker f₂
  rw [hker, h2, MonoidHom.range_eq_top.2 (actL_surjective hXW), Subgroup.card_top] at h1
  have hr : (Subgroup.inclusion hXL).range = X.subgroupOf L := by
    ext x
    simp only [MonoidHom.mem_range, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [h1, hf₁, MonoidHom.range_comp, hr]

theorem card_map_inf_eq_eight (h : Hyp331 G T M L D)
    (e : ↥(autOn L (vPlus L T)) ≃* alternatingGroup (Fin 7))
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card ↥(((T ⊓ L).subgroupOf L).map (actA7 (le_normalizer_vPlus h) e)) = 8 := by
  have hLV := le_normalizer_vPlus h
  have hTLs := isSylowTwoOf_inf h hTL
  have hP : IsPGroup 2 ((T ⊓ L).subgroupOf L) :=
    hTLs.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 (hP.map (actA7 hLV e))
  have hmul := (((T ⊓ L).subgroupOf L).map (actA7 hLV e)).card_mul_index
  rw [hk, CFSG.Quasithin.H.A7.card_A7] at hmul
  have hidx : ¬ 2 ∣ (((T ⊓ L).subgroupOf L).map (actA7 hLV e)).index := fun h2 =>
    hTLs.2.2 (h2.trans (Subgroup.index_map_dvd _ (actA7_surjective hLV e)))
  rw [hk]
  exact two_pow_eq_eight hmul hidx

theorem autOn_T_eq (h : Hyp331 G T M L D)
    (e : ↥(autOn L (vPlus L T)) ≃* alternatingGroup (Fin 7)) (hML : mPlus L T = L)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hc4 : Nat.card ↥⁅vPlus L T, L⁆ = 2 ^ 4) :
    autOn T ⁅vPlus L T, L⁆ = autOn (T ⊓ L) ⁅vPlus L T, L⁆ := by
  have := isMulCommutative_commV h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLW := le_normalizer_commV h
  have hTW := T_le_normalizer_commV hTL
  have hΓ := card_autOn_commV h e hML
  have hTΓ : autOn T ⁅vPlus L T, L⁆ ≤ autOn L ⁅vPlus L T, L⁆ := fun x hx =>
    A7.mem_of_mem_normalizer_four (mul_self_commV h) hc4 hΓ
      (CFSG.Quasithin.autOn_le_normalizer_autOn hTW hLW hTL hx)
  have hTL8 : Nat.card ↥(autOn (T ⊓ L) ⁅vPlus L T, L⁆) = 8 := by
    rw [card_autOn_eq_card_map h e hML inf_le_right, card_map_inf_eq_eight h e hTL]
  have hP : IsPGroup 2 ↥(autOn T ⁅vPlus L T, L⁆) := by
    have h1 : IsPGroup 2 ↥(T.subgroupOf (Subgroup.normalizer
        ((⁅vPlus L T, L⁆ : Subgroup G) : Set G))) :=
      h.sylow.1.comap_of_injective _ (Subgroup.subtype_injective _) |>.of_equiv
        (MulEquiv.refl _)
    exact h1.map _
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hP
  have hdvd : 2 ^ k ∣ 2520 := by
    rw [← hk, ← hΓ]
    exact Subgroup.card_dvd_of_le hTΓ
  have hk3 : k ≤ 3 := by
    by_contra hk3
    push Not at hk3
    have h16 : (16 : ℕ) ∣ 2520 := by
      have : (16 : ℕ) ∣ 2 ^ k := by
        rw [show (16 : ℕ) = 2 ^ 4 by norm_num]
        exact Nat.pow_dvd_pow 2 hk3
      exact this.trans hdvd
    norm_num at h16
  refine (Subgroup.eq_of_le_of_card_ge (CFSG.Quasithin.A4.autOn_mono inf_le_left) ?_).symm
  rw [hTL8, hk]
  calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
    _ = 8 := by norm_num

theorem exists_inf_conj_eq (h : Hyp331 G T M L D)
    (e : ↥(autOn L (vPlus L T)) ≃* alternatingGroup (Fin 7)) (hML : mPlus L T = L)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hc4 : Nat.card ↥⁅vPlus L T, L⁆ = 2 ^ 4)
    {t : G} (ht : t ∈ T) :
    ∃ s ∈ T ⊓ L, ∀ v ∈ vPlus L T, t * v * t⁻¹ = s * v * s⁻¹ := by
  have hTW := T_le_normalizer_commV hTL
  have hmem : CFSG.Quasithin.A4.actionOn ⁅vPlus L T, L⁆ T hTW ⟨t, ht⟩ ∈
      autOn T ⁅vPlus L T, L⁆ := (CFSG.Quasithin.A4.mem_autOn_iff hTW).2 ⟨⟨t, ht⟩, rfl⟩
  rw [autOn_T_eq h e hML hTL hc4] at hmem
  have hsW : T ⊓ L ≤ Subgroup.normalizer ((⁅vPlus L T, L⁆ : Subgroup G) : Set G) :=
    inf_le_left.trans hTW
  obtain ⟨⟨s, hs⟩, hseq⟩ := (CFSG.Quasithin.A4.mem_autOn_iff hsW).1 hmem
  refine ⟨s, hs, ?_⟩
  let E : Subgroup G :=
    { carrier := {v | t * v * t⁻¹ = s * v * s⁻¹}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        calc t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
          _ = (s * a * s⁻¹) * (s * b * s⁻¹) := by rw [ha, hb]
          _ = s * (a * b) * s⁻¹ := by group
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        calc t * a⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ := by group
          _ = (s * a * s⁻¹)⁻¹ := by rw [ha]
          _ = s * a⁻¹ * s⁻¹ := by group }
  have hWE : ⁅vPlus L T, L⁆ ≤ E := by
    intro w hw
    have := congrArg (fun a : MulAut ↥⁅vPlus L T, L⁆ => ((a ⟨w, hw⟩ : ↥⁅vPlus L T, L⁆) : G)) hseq
    exact this.symm
  have hZE : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) ≤ E := by
    intro z hz
    obtain ⟨hzZ, hzL⟩ := Subgroup.mem_inf.1 hz
    show t * z * t⁻¹ = s * z * s⁻¹
    have h1 := Subgroup.mem_centralizer_iff.1 (L246C127.le_centralizer_omegaOneCenter T ht) z hzZ
    have h2 := Subgroup.mem_centralizer_iff.1 hzL s (Subgroup.mem_inf.1 hs).2
    rw [← h1, mul_inv_cancel_right, h2, mul_inv_cancel_right]
  have hdec := h.vPlus_decomp.2
  rw [hML] at hdec
  intro v hv
  rw [hdec] at hv
  exact sup_le hWE hZE hv

omit [Finite G] in
theorem actL_eq_of_conj_eq {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (a b : ↥L) (hab : ∀ v ∈ V, (a : G) * v * (a : G)⁻¹ = b * v * (b : G)⁻¹) :
    actL L V hLV a = actL L V hLV b := by
  apply Subtype.ext
  ext v
  exact hab v v.2

omit [Finite G] in
theorem le_normalizer_of_conj_mem {K : Subgroup G}
    (hK : ∀ t ∈ T, ∀ k ∈ K, t * k * t⁻¹ ∈ K) : T ≤ Subgroup.normalizer (K : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨hK t ht k, fun hk => ?_⟩
  have := hK t⁻¹ (T.inv_mem ht) _ hk
  simpa [mul_assoc] using this

end Action

section MTwo

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique
open scoped IsMulCommutative

theorem exists_equiv_map_le_stabFS (h : Hyp331 G T M L D)
    (e : ↥(autOn L (vPlus L T)) ≃* alternatingGroup (Fin 7))
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    ∃ e' : ↥(autOn L (vPlus L T)) ≃* alternatingGroup (Fin 7),
      ((T ⊓ L).subgroupOf L).map (actA7 (le_normalizer_vPlus h) e') ≤ A7.stabA7 A7.vecFS := by
  obtain ⟨Q, hQ, hQ8⟩ := exists_card_eight_le_stabFS
  obtain ⟨g, hg⟩ := exists_conj_eq_of_card_eight (card_map_inf_eq_eight h e hTL) hQ8
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  have : actA7 (le_normalizer_vPlus h) (e.trans (MulAut.conj g)) =
      (MulAut.conj g).toMonoidHom.comp (actA7 (le_normalizer_vPlus h) e) := rfl
  rw [this, ← Subgroup.map_map, hg]
  exact hQ

theorem mTwo_facts
    (h10 : Stmt3_3_10) (h : Hyp331 G T M L D)
    (e : ↥(autOn L (vPlus L T)) ≃* alternatingGroup (Fin 7))
    (hQ : ((T ⊓ L).subgroupOf L).map (actA7 (le_normalizer_vPlus h) e) ≤ A7.stabA7 A7.vecFS)
    (hML : mPlus L T = L) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hc4 : Nat.card ↥⁅vPlus L T, L⁆ = 2 ^ 4) :
    L3316.liftCore (actA7 (le_normalizer_vPlus h) e) A7.altFive ∈ lFamilyOf L T ∧
      L3312.Type3312R (↥(L3316.liftCore (actA7 (le_normalizer_vPlus h) e) A7.altFive) ⧸
        CFSG.pCore 2 ↥(L3316.liftCore (actA7 (le_normalizer_vPlus h) e) A7.altFive)) ∧
      pCoreOf 2 (L3316.liftCore (actA7 (le_normalizer_vPlus h) e) A7.altFive ⊔ T ⊔ D) ≠ ⊥ ∧
      ¬ InducesInnerOn T (L3316.liftCore (actA7 (le_normalizer_vPlus h) e) A7.altFive) ∧
      ((L3316.liftCore (actA7 (le_normalizer_vPlus h) e) A7.altFive).subgroupOf L).map
        (actA7 (le_normalizer_vPlus h) e) = A7.altFive := by
  have hLV := le_normalizer_vPlus h
  set φ := actA7 hLV e with hφ
  set P := A7.altFive with hPdef
  set M₂ := L3316.liftCore φ P with hM₂
  have hφs : Function.Surjective φ := actA7_surjective hLV e
  have := A7.isSimpleGroup_altFive
  have hnc := A7.altFive_nonabelian
  have hPperf : perfectCore P = P := perfectCore_eq_self_of_perfect A7.commutator_altFive
  have hM₂L : M₂ ≤ L := L3316.liftCore_le φ P
  have hsub : M₂.subgroupOf L = perfectCore (P.comap φ) := by
    rw [hM₂, L3316.liftCore_eq]
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  have hmap : (M₂.subgroupOf L).map φ = P := by
    rw [hsub, L3316.map_perfectCore_comap hφs, hPperf]
  have hfm : ∀ x : ↥M₂, φ (Subgroup.inclusion hM₂L x) ∈ P := fun x =>
    hmap ▸ Subgroup.mem_map_of_mem φ (show Subgroup.inclusion hM₂L x ∈ M₂.subgroupOf L from x.2)
  set f : ↥M₂ →* ↥P := (φ.comp (Subgroup.inclusion hM₂L)).codRestrict P hfm with hf
  have hfs : Function.Surjective f := by
    rintro ⟨p, hp⟩
    rw [← hmap] at hp
    obtain ⟨y, hy, hyp⟩ := hp
    exact ⟨⟨(y : G), hy⟩, Subtype.ext hyp⟩
  have hfk : ∀ y : ↥M₂, f y = 1 ↔ (y : G) ∈ Subgroup.centralizer (vPlus L T : Set G) := by
    intro y
    have h1 : f y = 1 ↔ φ (Subgroup.inclusion hM₂L y) = 1 :=
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [h1, ← MonoidHom.mem_ker, hφ, actA7_ker, Subgroup.mem_subgroupOf]
    rfl
  have h2 : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier ↥P) = 2 := by
    rw [← card_hopfMultiplier_congr A7.altFiveEquiv, card_hopfMultiplier_alt5]
  have hTpre : T ≤ Subgroup.normalizer (L3316.liftPre φ P : Set G) := by
    refine le_normalizer_of_conj_mem fun t ht l hl => ?_
    obtain ⟨y, hyP, rfl⟩ := hl
    obtain ⟨s, hs, hconj⟩ := exists_inf_conj_eq h e hML hTL hc4 ht
    have hsL : s ∈ L := (Subgroup.mem_inf.1 hs).2
    have htyL : t * (y : G) * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hTL ht) y).1 y.2
    have hsyL : s * (y : G) * s⁻¹ ∈ L := L.mul_mem (L.mul_mem hsL y.2) (L.inv_mem hsL)
    have hact : actL L (vPlus L T) hLV ⟨_, htyL⟩ = actL L (vPlus L T) hLV ⟨_, hsyL⟩ := by
      refine actL_eq_of_conj_eq hLV _ _ fun v hv => ?_
      have hTV := Hyp331.le_normalizer_vPlus L T
      have hv1 : t⁻¹ * v * t ∈ vPlus L T := by
        have := (Subgroup.mem_normalizer_iff.1 (hTV (T.inv_mem ht)) v).1 hv
        simpa using this
      have h1 : t⁻¹ * v * t = s⁻¹ * v * s := by
        have := hconj _ hv1
        calc t⁻¹ * v * t = s⁻¹ * (s * (t⁻¹ * v * t) * s⁻¹) * s := by group
          _ = s⁻¹ * (t * (t⁻¹ * v * t) * t⁻¹) * s := by rw [this]
          _ = s⁻¹ * v * s := by group
      have hv2 : (y : G) * (s⁻¹ * v * s) * (y : G)⁻¹ ∈ vPlus L T := by
        have hv3 : s⁻¹ * v * s ∈ vPlus L T := by
          have := (Subgroup.mem_normalizer_iff.1 (hLV (L.inv_mem hsL)) v).1 hv
          simpa using this
        exact (Subgroup.mem_normalizer_iff.1 (hLV y.2) _).1 hv3
      show (t * (y : G) * t⁻¹) * v * (t * (y : G) * t⁻¹)⁻¹ =
        (s * (y : G) * s⁻¹) * v * (s * (y : G) * s⁻¹)⁻¹
      calc (t * (y : G) * t⁻¹) * v * (t * (y : G) * t⁻¹)⁻¹ =
          t * ((y : G) * (t⁻¹ * v * t) * (y : G)⁻¹) * t⁻¹ := by group
        _ = t * ((y : G) * (s⁻¹ * v * s) * (y : G)⁻¹) * t⁻¹ := by rw [h1]
        _ = s * ((y : G) * (s⁻¹ * v * s) * (y : G)⁻¹) * s⁻¹ := hconj _ hv2
        _ = (s * (y : G) * s⁻¹) * v * (s * (y : G) * s⁻¹)⁻¹ := by group
    have hφeq : φ ⟨_, htyL⟩ = φ ⟨s, hsL⟩ * φ y * (φ ⟨s, hsL⟩)⁻¹ := by
      have : φ ⟨_, htyL⟩ = φ ⟨_, hsyL⟩ := by
        simp only [hφ, actA7, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
          hact]
      rw [this, ← map_inv, ← map_mul, ← map_mul]
      rfl
    have hsQ : φ ⟨s, hsL⟩ ∈ A7.stabA7 A7.vecFS :=
      hQ (Subgroup.mem_map_of_mem φ (show (⟨s, hsL⟩ : ↥L) ∈ (T ⊓ L).subgroupOf L from hs))
    refine ⟨⟨_, htyL⟩, ?_, rfl⟩
    show φ ⟨_, htyL⟩ ∈ P
    rw [hφeq]
    exact (Subgroup.mem_normalizer_iff.1 (stabFS_le_normalizer_altFive hsQ) _).1 hyP
  have hTM₂ : T ≤ Subgroup.normalizer (M₂ : Set G) := fun t ht =>
    L3316.mem_normalizer_perfectCore (hTpre ht)
  obtain ⟨hmem, ⟨eQ⟩⟩ := mem_lFamilyOf_of_hopf h e hM₂L (L3316.liftCore_perfect φ P) hTM₂ hnc h2
    f hfs hfk
  have hcen : ∀ x ∈ L, x ∈ Subgroup.centralizer (vPlus L T : Set G) → ∀ y ∈ L,
      x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 L := fun x hx hxV y hy =>
    CFSG.Quasithin.H13.A7.commutator_mem_pCoreOf_of_ker h.Lq (actA7_surjective hLV e)
      (actA7_ker hLV e) hx hxV hy
  have hk := ker_eq_pCore_of_hopf hM₂L (L3316.liftCore_perfect φ P) hcen hnc h2 f hfs hfk
  refine ⟨hmem, Or.inl ⟨2, le_rfl, C126.isPSL_two_two_two_of_alternating_five _
    ⟨eQ.trans A7.altFiveEquiv.symm⟩⟩, ?_, ?_, hmap⟩
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hK4 : Nat.card (GaloisField 2 2) = 4 := by
      rw [GaloisField.card 2 2 (by norm_num)]
      norm_num
    obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
      (GaloisField 2 2) (Or.inl hK4)
    obtain ⟨e2⟩ := CFSG.RankThree.PartOne.nonempty_SL2_mulEquiv_statedProj'
      (F := GaloisField 2 2)
    set f' : ↥M₂ →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) :=
      ((A7.altFiveEquiv.symm.trans e5.symm).trans e2.symm).toMonoidHom.comp f with hf'
    have hf's : Function.Surjective f' := by
      rw [hf', MonoidHom.coe_comp]
      exact (MulEquiv.surjective _).comp hfs
    have hk' : IsPGroup 2 ↥f'.ker := by
      have : f'.ker = f.ker := by
        ext x
        simp only [hf', MonoidHom.mem_ker, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
          Function.comp_apply, MulEquiv.map_eq_one_iff]
      rw [this, hk]
      exact CFSG.pCore_isPGroup
    exact L3316.pCoreOf_sup_ne_bot h10 h hTM₂ hmem.2.2.2.2 hK4.ge hf's hk'
  ·
    intro hInn
    have hnle : ¬ ((T ⊓ L).subgroupOf L).map φ ≤ P := by
      intro hle
      have hd := Subgroup.card_dvd_of_le hle
      rw [card_map_inf_eq_eight h e hTL, A7.nat_card_altFive] at hd
      norm_num at hd
    obtain ⟨q, hqQ, hqP⟩ := Set.not_subset.1 hnle
    obtain ⟨s₀, hs₀, rfl⟩ := hqQ
    have hs₀T : (s₀ : G) ∈ T := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hs₀)).1
    obtain ⟨y, hyM, hy⟩ := hInn (s₀ : G) hs₀T
    have hO : ∀ z ∈ pCoreOf 2 M₂, ∀ hzL : z ∈ L, φ ⟨z, hzL⟩ = 1 := by
      intro z hz hzL
      rw [CFSG.Quasithin.H13.A7.pCoreOf_eq_map_cfsgPCore] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      rw [← hk] at hw
      exact congrArg Subtype.val (show f w = 1 from hw)
    set y' : ↥L := ⟨y, hM₂L hyM⟩ with hy'
    have hpP : φ y' ∈ P := hfm ⟨y, hyM⟩
    have hact : ∀ π ∈ P, φ s₀ * π * (φ s₀)⁻¹ = φ y' * π * (φ y')⁻¹ := by
      intro π hπ
      obtain ⟨x, hx⟩ := hfs ⟨π, hπ⟩
      have hxπ : φ (Subgroup.inclusion hM₂L x) = π := congrArg Subtype.val hx
      set x' : ↥L := Subgroup.inclusion hM₂L x with hx'
      have hc := hy (x : G) x.2
      have hcL : (s₀ : G) * x * (s₀ : G)⁻¹ * ((y : G) * x * y⁻¹)⁻¹ ∈ L :=
        (s₀ * x' * s₀⁻¹ * (y' * x' * y'⁻¹)⁻¹).2
      have h1 := hO _ hc hcL
      have h2 : (⟨_, hcL⟩ : ↥L) = s₀ * x' * s₀⁻¹ * (y' * x' * y'⁻¹)⁻¹ := rfl
      rw [h2, map_mul, map_inv, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hxπ] at h1
      exact mul_inv_eq_one.1 h1
    have hcomm : ∀ ρ ∈ P, ((φ y')⁻¹ * φ s₀) * ρ = ρ * ((φ y')⁻¹ * φ s₀) := by
      intro ρ hρ
      have := hact ρ hρ
      calc ((φ y')⁻¹ * φ s₀) * ρ = (φ y')⁻¹ * (φ s₀ * ρ * (φ s₀)⁻¹) * φ s₀ := by group
        _ = (φ y')⁻¹ * (φ y' * ρ * (φ y')⁻¹) * φ s₀ := by rw [this]
        _ = ρ * ((φ y')⁻¹ * φ s₀) := by group
    have h1 := eq_one_of_commute_altFive hcomm
    apply hqP
    rw [inv_mul_eq_one] at h1
    rw [← h1]
    exact hpP

end MTwo

section Gen

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique
open scoped commutatorElement

theorem eq_top_of_dvd_card {X : Subgroup (alternatingGroup (Fin 7))}
    (h168 : 168 ∣ Nat.card X) (h60 : 60 ∣ Nat.card X) : X = ⊤ := by
  have h840 : 840 ∣ Nat.card X := by
    have := Nat.lcm_dvd h168 h60
    rwa [show Nat.lcm 168 60 = 840 by norm_num] at this
  have hmul := X.card_mul_index
  rw [CFSG.Quasithin.H.A7.card_A7] at hmul
  obtain ⟨k, hk⟩ := h840
  rw [hk] at hmul
  have hk3 : k * X.index = 3 := by
    have : 840 * (k * X.index) = 840 * 3 := by rw [← mul_assoc, hmul]
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  by_contra hne
  have hcore : X.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal X.normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ X.normalCore_le)) hne
  have hinj : Function.Injective (MulAction.toPermHom (alternatingGroup (Fin 7))
      (alternatingGroup (Fin 7) ⧸ X)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker, hcore]
  have hle : Nat.card (alternatingGroup (Fin 7)) ≤ X.index.factorial := by
    calc Nat.card (alternatingGroup (Fin 7)) ≤ Nat.card (Perm (alternatingGroup (Fin 7) ⧸ X)) :=
          Nat.card_le_card_of_injective _ hinj
      _ = X.index.factorial := by rw [Nat.card_perm, Subgroup.index_eq_card]
  rw [CFSG.Quasithin.H.A7.card_A7] at hle
  have hi : X.index ≤ 3 := Nat.le_of_dvd (by norm_num) ⟨k, by rw [← hk3]; ring⟩
  have h6 := Nat.factorial_le hi
  rw [show Nat.factorial 3 = 6 by rfl] at h6
  omega

omit [Finite G] in
theorem le_sup_pCoreOf {L H : Subgroup G} {X : Type*} [Group X] (hL : ⁅L, L⁆ = L)
    (φ : ↥L →* X) (hH : (H.subgroupOf L).map φ = φ.range)
    (hcen : ∀ x : ↥L, φ x = 1 → ∀ y ∈ L, (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈ pCoreOf 2 L) :
    L ≤ H ⊔ pCoreOf 2 L := by
  set P := CFSG.pCore 2 ↥L with hP
  have hPL : pCoreOf 2 L = P.map L.subtype := CFSG.Quasithin.H13.A7.pCoreOf_eq_map_cfsgPCore 2 L
  have hcz : ∀ c : ↥L, φ c = 1 →
      (QuotientGroup.mk c : ↥L ⧸ P) ∈ Subgroup.center (↥L ⧸ P) := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 := hcen c hc y y.2
    rw [hPL] at h1
    obtain ⟨w, hw, hweq⟩ := h1
    have hw' : w = c * y * c⁻¹ * y⁻¹ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; exact hweq)
    rw [hw'] at hw
    have h2 : (QuotientGroup.mk (c * y * c⁻¹ * y⁻¹) : ↥L ⧸ P) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hw
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv] at h2
    calc (QuotientGroup.mk y : ↥L ⧸ P) * QuotientGroup.mk c
        = ((QuotientGroup.mk c * QuotientGroup.mk y * (QuotientGroup.mk c)⁻¹ *
            (QuotientGroup.mk y)⁻¹)⁻¹ * (QuotientGroup.mk c * QuotientGroup.mk y)) := by group
      _ = QuotientGroup.mk c * QuotientGroup.mk y := by rw [h2, inv_one, one_mul]
  have hdec : ∀ a : ↥L, ∃ b : ↥L, (b : G) ∈ H ∧ φ (b⁻¹ * a) = 1 := by
    intro a
    have ha : φ a ∈ (H.subgroupOf L).map φ := hH ▸ ⟨a, rfl⟩
    obtain ⟨b, hb, hba⟩ := ha
    exact ⟨b, hb, by rw [map_mul, map_inv, hba, inv_mul_cancel]⟩
  refine le_trans (le_of_eq hL.symm) ?_
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨a', ha'H, ha'⟩ := hdec ⟨a, ha⟩
  obtain ⟨b', hb'H, hb'⟩ := hdec ⟨b, hb⟩
  have hq : (QuotientGroup.mk ⁅(⟨a, ha⟩ : ↥L), ⟨b, hb⟩⁆ : ↥L ⧸ P) =
      QuotientGroup.mk ⁅a', b'⁆ := by
    obtain ⟨ca, hca, hca1⟩ : ∃ c : ↥L, (⟨a, ha⟩ : ↥L) = a' * c ∧ φ c = 1 :=
      ⟨a'⁻¹ * ⟨a, ha⟩, by group, ha'⟩
    obtain ⟨cb, hcb, hcb1⟩ : ∃ c : ↥L, (⟨b, hb⟩ : ↥L) = b' * c ∧ φ c = 1 :=
      ⟨b'⁻¹ * ⟨b, hb⟩, by group, hb'⟩
    rw [hca, hcb, ← QuotientGroup.mk'_apply, ← QuotientGroup.mk'_apply, map_commutatorElement,
      map_commutatorElement, map_mul, map_mul]
    exact CFSG.SectionRank.commutatorElement_mul_mem_center _ _ (hcz _ hca1) (hcz _ hcb1)
  have hmem : ⁅a', b'⁆⁻¹ * ⁅(⟨a, ha⟩ : ↥L), ⟨b, hb⟩⁆ ∈ P :=
    (QuotientGroup.eq).1 hq.symm
  have hfin : ⁅a, b⁆ = ((⁅a', b'⁆ : ↥L) : G) *
      ((⁅a', b'⁆⁻¹ * ⁅(⟨a, ha⟩ : ↥L), ⟨b, hb⟩⁆ : ↥L) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    group
  rw [hfin]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
  · show (a' : G) * b' * (a' : G)⁻¹ * (b' : G)⁻¹ ∈ H
    exact H.mul_mem (H.mul_mem (H.mul_mem ha'H hb'H) (H.inv_mem ha'H)) (H.inv_mem hb'H)
  · rw [hPL]
    exact ⟨_, hmem, rfl⟩

theorem pCoreOf_L_le_T (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    pCoreOf 2 L ≤ T :=
  (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T)
    le_sup_left ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hTL))).trans
    (EscapingLocal.pCoreOf_le_of_isSylowTwoOf
      (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow le_sup_right))

theorem sup_eq_mOne_mTwo
    (h10 : Stmt3_3_10) (h : Hyp331 G T M L D)
    (e : ↥(autOn L (vPlus L T)) ≃* alternatingGroup (Fin 7))
    (hQ : ((T ⊓ L).subgroupOf L).map (actA7 (le_normalizer_vPlus h) e) ≤ A7.stabA7 A7.vecFS)
    (hML : mPlus L T = L) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hc4 : Nat.card ↥⁅vPlus L T, L⁆ = 2 ^ 4) :
    L ⊔ T = mOne L T ⊔ L3316.liftCore (actA7 (le_normalizer_vPlus h) e) A7.altFive ⊔ T := by
  have hLV := le_normalizer_vPlus h
  set φ := actA7 hLV e with hφ
  set M₂ := L3316.liftCore φ A7.altFive with hM₂
  have hM₂L : M₂ ≤ L := L3316.liftCore_le _ _
  obtain ⟨-, -, -, -, h168⟩ := mOne_facts (D := D) h e hML hTL hc4
  obtain ⟨-, -, -, -, hmap2⟩ := mTwo_facts h10 h e hQ hML hTL hc4
  have hmap1 : Nat.card ↥(((mOne L T).subgroupOf L).map φ) = 168 := by
    rw [← card_autOn_eq_card_map h e hML (mOne_le L T), h168]
  set H := mOne L T ⊔ M₂ with hH
  have htop : (H.subgroupOf L).map φ = ⊤ := by
    refine eq_top_of_dvd_card ?_ ?_
    · rw [← hmap1]
      exact Subgroup.card_dvd_of_le (Subgroup.map_mono (Subgroup.subgroupOf_mono L le_sup_left))
    · have h60 : Nat.card ↥A7.altFive = 60 := A7.nat_card_altFive
      rw [← h60, ← hmap2]
      exact Subgroup.card_dvd_of_le (Subgroup.map_mono (Subgroup.subgroupOf_mono L le_sup_right))
  have hcen : ∀ x : ↥L, φ x = 1 → ∀ y ∈ L, (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈ pCoreOf 2 L := by
    intro x hx y hy
    have hxV : (x : G) ∈ Subgroup.centralizer (vPlus L T : Set G) := by
      rw [← MonoidHom.mem_ker, hφ, actA7_ker, Subgroup.mem_subgroupOf] at hx
      exact hx
    exact CFSG.Quasithin.H13.A7.commutator_mem_pCoreOf_of_ker h.Lq (actA7_surjective hLV e)
      (actA7_ker hLV e) x.2 hxV hy
  have hle := le_sup_pCoreOf h.toSetup331.perfect φ
    (by rw [htop, MonoidHom.range_eq_top.2 (actA7_surjective hLV e)]) hcen
  have hOT := pCoreOf_L_le_T h hTL
  refine le_antisymm (sup_le (hle.trans (sup_le le_sup_left (hOT.trans le_sup_right)))
    le_sup_right) (sup_le (sup_le ?_ ?_) le_sup_right)
  · exact (mOne_le L T).trans le_sup_left
  · exact hM₂L.trans le_sup_left

end Gen

end CFSG.Quasithin.H13.L3317
