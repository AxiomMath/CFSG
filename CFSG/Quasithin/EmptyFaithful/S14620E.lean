module

public import CFSG.Quasithin.EmptyFaithful.S14620D
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSG.Quasithin.EmptyFaithful.S14620EK

public section

namespace CFSG.Quasithin

open Pointwise
open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.C2Push CFSG.LieType.BorelTits
  CFSG.GroupTheory.AutAlternating

section Finite7

private abbrev P7 : Type := Equiv.Perm (Fin 7)

private def f7a : Subgroup P7 := MulAction.stabilizer P7 ({4, 5, 6} : Finset (Fin 7))
private def f7b : Subgroup P7 :=
  MulAction.stabilizer P7 ({{0, 1}, {2, 3}, {4, 5}, {6}} : Finset (Finset (Fin 7)))

private instance : DecidablePred (· ∈ f7a) := fun g =>
  inferInstanceAs (Decidable (g • ({4, 5, 6} : Finset (Fin 7)) = {4, 5, 6}))
private instance : DecidablePred (· ∈ f7b) := fun g =>
  inferInstanceAs (Decidable (g • ({{0, 1}, {2, 3}, {4, 5}, {6}} : Finset (Finset (Fin 7))) =
    {{0, 1}, {2, 3}, {4, 5}, {6}}))
private instance : DecidablePred (· ∈ f7a ⊓ f7b) := fun g => inferInstanceAs (Decidable (g ∈ f7a ∧ g ∈ f7b))

private theorem card_f7a : Fintype.card f7a = 144 := by
  rw [← S14620EK.card_a, ← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun g =>
    MulAction.mem_stabilizer_iff.trans (S14620EK.stabA_iff g))
private theorem card_f7b : Fintype.card f7b = 48 := by
  rw [← S14620EK.card_b, ← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun g =>
    MulAction.mem_stabilizer_iff.trans (S14620EK.stabB_iff g))
private theorem card_f7ab : Fintype.card ↥(f7a ⊓ f7b) = 16 := by
  rw [← S14620EK.card_ab, ← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun g =>
    Subgroup.mem_inf.trans ((and_congr MulAction.mem_stabilizer_iff
      MulAction.mem_stabilizer_iff).trans (S14620EK.qAB_iff g)))

private theorem mem_f7a_iff (g : P7) : g ∈ f7a ↔ g • ({4, 5, 6} : Finset (Fin 7)) = {4, 5, 6} :=
  MulAction.mem_stabilizer_iff

private theorem coatom_f7a : IsCoatom f7a := by
  have h := Equiv.Perm.isCoatom_stabilizer_of_ncard_lt_ncard_compl (α := Fin 7)
    (s := (({4, 5, 6} : Finset (Fin 7)) : Set (Fin 7))) (by simp) (by
      have := Set.ncard_add_ncard_compl (({4, 5, 6} : Finset (Fin 7)) : Set (Fin 7))
      simp at this ⊢
      omega)
  convert h using 2
  ext g
  rw [mem_f7a_iff, MulAction.mem_stabilizer_iff, ← Finset.coe_smul_finset, Finset.coe_inj]

private def g₀ : P7 := Equiv.swap 2 4 * Equiv.swap 3 5

private theorem g₀_mem_f7b : g₀ ∈ f7b := by
  show g₀ • ({{0, 1}, {2, 3}, {4, 5}, {6}} : Finset (Finset (Fin 7))) = {{0, 1}, {2, 3}, {4, 5}, {6}}
  decide +kernel

private theorem g₀_not_mem_f7a : g₀ ∉ f7a := by
  rw [mem_f7a_iff]
  decide +kernel

private theorem g₀_even : g₀ ∈ alternatingGroup (Fin 7) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

private theorem not_f7b_le_f7a : ¬ f7b ≤ f7a := fun h => g₀_not_mem_f7a (h g₀_mem_f7b)

private theorem f7a_sup_f7b : f7a ⊔ f7b = ⊤ :=
  coatom_f7a.2 _ (lt_of_le_of_ne le_sup_left fun h => not_f7b_le_f7a (by rw [h]; exact le_sup_right))

private theorem isSolvable_f7a : Group.IsSolvable ↥f7a := by
  have : Finite ↥f7a := inferInstance
  exact CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
    (by rw [Nat.card_eq_fintype_card, card_f7a]; norm_num [Nat.primeFactors])

private theorem isSolvable_f7b : Group.IsSolvable ↥f7b := by
  have : Finite ↥f7b := inferInstance
  exact CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
    (by rw [Nat.card_eq_fintype_card, card_f7b]; norm_num [Nat.primeFactors])

private theorem isSolvable_of_le' {G : Type*} [Group G] {A B : Subgroup G} (h : A ≤ B)
    (hB : Group.IsSolvable ↥B) : Group.IsSolvable ↥A :=
  Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion h) (Subgroup.inclusion_injective h)

private theorem card_perm7 : Nat.card P7 = 5040 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  norm_num

private theorem isSylowTwoOf_f7ab : IsSylowTwoOf (f7a ⊓ f7b) ⊤ := by
  have hc : Nat.card ↥(f7a ⊓ f7b) = 16 := by rw [Nat.card_eq_fintype_card, card_f7ab]
  refine ⟨le_top, IsPGroup.of_card (n := 4) (by rw [hc]; norm_num), ?_⟩
  have h1 : ((f7a ⊓ f7b).subgroupOf ⊤).index = (f7a ⊓ f7b).index :=
    Subgroup.relIndex_top_right (f7a ⊓ f7b)
  have h2 := Subgroup.card_mul_index (f7a ⊓ f7b)
  rw [hc, card_perm7] at h2
  intro hdvd
  rw [h1] at hdvd
  omega

private theorem coatom_f7a_alt : IsCoatom (f7a.subgroupOf (alternatingGroup (Fin 7))) := by
  have h := alternatingGroup.isCoatom_stabilizer (α := Fin 7)
    (s := (({4, 5, 6} : Finset (Fin 7)) : Set (Fin 7))) (by simp) (by
      rw [Set.nonempty_iff_ne_empty]
      intro hc
      have := congrArg Set.ncard hc
      have h2 := Set.ncard_add_ncard_compl (({4, 5, 6} : Finset (Fin 7)) : Set (Fin 7))
      simp at this h2
      omega) (by
      have h2 := Set.ncard_add_ncard_compl (({4, 5, 6} : Finset (Fin 7)) : Set (Fin 7))
      simp at h2 ⊢)
  convert h using 2
  ext x
  rw [Subgroup.mem_subgroupOf, mem_f7a_iff, MulAction.mem_stabilizer_iff, ← Finset.coe_smul_finset,
    Finset.coe_inj]
  exact Iff.rfl

private theorem f7_alt_join :
    (f7a ⊓ alternatingGroup (Fin 7)) ⊔ (f7b ⊓ alternatingGroup (Fin 7)) =
      alternatingGroup (Fin 7) := by
  set A := alternatingGroup (Fin 7) with hAdef
  set J := (f7a ⊓ A) ⊔ (f7b ⊓ A) with hJ
  have hJA : J ≤ A := sup_le inf_le_right inf_le_right
  have h1 : f7a.subgroupOf A ≤ J.subgroupOf A := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (le_sup_left (a := f7a ⊓ A) (b := f7b ⊓ A)
      ⟨Subgroup.mem_subgroupOf.mp hx, x.2⟩)
  rcases eq_or_lt_of_le h1 with heq | hlt
  · exfalso
    have hg : (⟨g₀, g₀_even⟩ : ↥A) ∈ J.subgroupOf A :=
      Subgroup.mem_subgroupOf.mpr (le_sup_right (a := f7a ⊓ A) (b := f7b ⊓ A) ⟨g₀_mem_f7b, g₀_even⟩)
    rw [← heq] at hg
    exact g₀_not_mem_f7a (Subgroup.mem_subgroupOf.mp hg)
  · have htop : J.subgroupOf A = ⊤ := coatom_f7a_alt.2 _ hlt
    refine le_antisymm hJA fun x hx => ?_
    have : (⟨x, hx⟩ : ↥A) ∈ J.subgroupOf A := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.mp this

private theorem alt_conjSub (g : P7) : conjSub g (alternatingGroup (Fin 7)) = alternatingGroup (Fin 7) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp
    ((Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (alternatingGroup (Fin 7)).Normal)) ▸
      Subgroup.mem_top g)

private theorem exists_overgroups_perm7 {Y' T'' : Subgroup P7} (hY : alternatingGroup (Fin 7) ≤ Y')
    (hT : T'' ≤ Y') (hT2 : IsPGroup 2 ↥T'') :
    ∃ E₁ E₂ : Subgroup P7, T'' ≤ E₁ ∧ T'' ≤ E₂ ∧ E₁ ≤ Y' ∧ E₂ ≤ Y' ∧ Group.IsSolvable ↥E₁ ∧
      Group.IsSolvable ↥E₂ ∧ E₁ ⊔ E₂ = Y' := by
  have hdich : Y' = alternatingGroup (Fin 7) ∨ Y' = ⊤ := by
    have h1 : Y'.index ∣ 2 := alternatingGroup.index_eq_two (α := Fin 7) ▸ Subgroup.index_dvd_of_le hY
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · right
      exact Subgroup.index_eq_one.mp h
    · left
      exact Equiv.Perm.eq_alternatingGroup_of_index_eq_two h
  obtain ⟨S, hS, hTS⟩ := A4.exists_isSylowTwoOf_ge (le_top : T'' ≤ ⊤) hT2
  obtain ⟨g, -, hg⟩ := A4.exists_conj_of_isSylowTwoOf isSylowTwoOf_f7ab hS
  have hTc : T'' ≤ conjSub g (f7a ⊓ f7b) := fun x hx => mem_conjSub.mpr ((hg x).mp (hTS hx))
  have hTa : T'' ≤ conjSub g f7a := hTc.trans (conjSub_mono g inf_le_left)
  have hTb : T'' ≤ conjSub g f7b := hTc.trans (conjSub_mono g inf_le_right)
  have hsa : Group.IsSolvable ↥(conjSub g f7a) := isSolvable_conjSub g f7a isSolvable_f7a
  have hsb : Group.IsSolvable ↥(conjSub g f7b) := isSolvable_conjSub g f7b isSolvable_f7b
  rcases hdich with rfl | rfl
  · refine ⟨conjSub g f7a ⊓ alternatingGroup (Fin 7), conjSub g f7b ⊓ alternatingGroup (Fin 7),
      le_inf hTa hT, le_inf hTb hT, inf_le_right, inf_le_right, isSolvable_of_le' inf_le_left hsa,
      isSolvable_of_le' inf_le_left hsb, ?_⟩
    have h1 : conjSub g f7a ⊓ alternatingGroup (Fin 7) = conjSub g (f7a ⊓ alternatingGroup (Fin 7)) := by
      rw [conjSub_inf, alt_conjSub]
    have h2 : conjSub g f7b ⊓ alternatingGroup (Fin 7) = conjSub g (f7b ⊓ alternatingGroup (Fin 7)) := by
      rw [conjSub_inf, alt_conjSub]
    rw [h1, h2, ← conjSub_sup, f7_alt_join, alt_conjSub]
  · refine ⟨conjSub g f7a, conjSub g f7b, hTa, hTb, le_top, le_top, hsa, hsb, ?_⟩
    rw [← conjSub_sup, f7a_sup_f7b]
    exact Subgroup.map_top_of_surjective _ (MulEquiv.surjective _)

end Finite7

section Embed

private theorem exists_injective_perm7 {Y : Type*} [Group Y] {Kh : Subgroup Y} [Kh.Normal]
    (e : ↥Kh ≃* alternatingGroup (Fin 7)) (hC : ∀ x : Y, (∀ k ∈ Kh, x * k = k * x) → x = 1) :
    ∃ ψ : Y →* Equiv.Perm (Fin 7), Function.Injective ψ ∧ alternatingGroup (Fin 7) ≤ ψ.range := by
  let φ : Y →* MulAut ↥Kh := MulAut.conjNormal
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    refine hC x fun k hk => ?_
    have h1 : φ x = 1 := hx
    have h2 := congrArg (fun f : MulAut ↥Kh => (f ⟨k, hk⟩ : ↥Kh).1) h1
    simp [φ, MulAut.conjNormal_apply] at h2
    calc x * k = (x * k * x⁻¹) * x := by group
      _ = k * x := by rw [h2]
  let c : Equiv.Perm (Fin 7) →* MulAut (alternatingGroup (Fin 7)) := MulAut.conjNormal
  have hc : Function.Bijective c := aut_alternatingGroup_bijective_conj 7 (by norm_num) (by norm_num)
  let eAut : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) := MulEquiv.ofBijective c hc
  let ψ : Y →* Equiv.Perm (Fin 7) :=
    eAut.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp φ)
  refine ⟨ψ, ?_, ?_⟩
  · intro x y hxy
    apply hφ
    have := eAut.symm.injective hxy
    exact (MulAut.congr e).injective this
  · intro σ hσ
    refine ⟨(e.symm ⟨σ, hσ⟩ : Kh), ?_⟩
    show eAut.symm ((MulAut.congr e) (φ (e.symm ⟨σ, hσ⟩ : Kh))) = σ
    rw [MulEquiv.symm_apply_eq]
    refine MulEquiv.ext fun b => ?_
    have hk : (MulAut.conjNormal (↑(e.symm ⟨σ, hσ⟩ : ↥Kh) : Y)) (e.symm b) =
        e.symm ⟨σ, hσ⟩ * e.symm b * (e.symm ⟨σ, hσ⟩)⁻¹ :=
      Subtype.ext (by simp [MulAut.conjNormal_apply])
    show e ((MulAut.conjNormal (↑(e.symm ⟨σ, hσ⟩ : ↥Kh) : Y)) (e.symm b)) = (c σ) b
    rw [hk, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    simp [c, MulAut.conjNormal_apply]


end Embed


section Alt7

private theorem trivial_centre_of_mulEquiv {Y : Type*} [Group Y] {L : Subgroup Y} {M : Type*} [Group M]
    (e : ↥L ≃* M) (hM : ∀ x : M, (∀ y, y * x = x * y) → x = 1) :
    ∀ x ∈ L, (∀ y ∈ L, y * x = x * y) → x = 1 := by
  intro x hx hc
  have h1 : e ⟨x, hx⟩ = 1 := by
    refine hM _ fun y => ?_
    have hy := hc (e.symm y : ↥L) (e.symm y).2
    have h2 : (e.symm y) * (⟨x, hx⟩ : ↥L) = (⟨x, hx⟩ : ↥L) * (e.symm y) := Subtype.ext hy
    have h3 := congrArg e h2
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
  have : (⟨x, hx⟩ : ↥L) = 1 := e.injective (by rw [h1, map_one])
  exact congrArg Subtype.val this

private theorem alt7_center_trivial :
    ∀ x : alternatingGroup (Fin 7), (∀ y, y * x = x * y) → x = 1 := by
  intro x hx
  have hxc : x ∈ Subgroup.center (alternatingGroup (Fin 7)) := Subgroup.mem_center_iff.mpr hx
  rw [alternatingGroup.center_eq_bot (by simp)] at hxc
  exact Subgroup.mem_bot.mp hxc

end Alt7


section Alt7Main

variable {G : Type} [Group G] [Finite G]

private theorem exists_two_solvable_overgroups_alt7 {Y : Type*} [Group Y] [Finite Y] {Kh : Subgroup Y}
    [Kh.Normal] (e : ↥Kh ≃* alternatingGroup (Fin 7))
    (hC : ∀ x : Y, (∀ k ∈ Kh, x * k = k * x) → x = 1) {T' : Subgroup Y} (hT : IsPGroup 2 ↥T') :
    ∃ E₁ E₂ : Subgroup Y, T' ≤ E₁ ∧ T' ≤ E₂ ∧ Group.IsSolvable ↥E₁ ∧ Group.IsSolvable ↥E₂ ∧
      E₁ ⊔ E₂ = ⊤ := by
  obtain ⟨ψ, hψ, hA⟩ := exists_injective_perm7 e hC
  obtain ⟨E₁, E₂, h1, h2, hE₁, hE₂, hs1, hs2, hsup⟩ :=
    exists_overgroups_perm7 (Y' := ψ.range) (T'' := T'.map ψ) hA
      (Subgroup.map_le_range ψ T') (hT.map ψ)
  have hsolv : ∀ E : Subgroup (Equiv.Perm (Fin 7)), Group.IsSolvable ↥E →
      Group.IsSolvable ↥(E.comap ψ) := fun E hE =>
    Group.isSolvable_of_isSolvable_injective (f := ψ.subgroupComap E) fun x y hxy =>
      Subtype.ext (hψ (congrArg Subtype.val hxy))
  refine ⟨E₁.comap ψ, E₂.comap ψ, Subgroup.map_le_iff_le_comap.mp h1,
    Subgroup.map_le_iff_le_comap.mp h2, hsolv E₁ hs1, hsolv E₂ hs2, ?_⟩
  apply Subgroup.map_injective hψ
  rw [Subgroup.map_sup, Subgroup.map_comap_eq_self hE₁, Subgroup.map_comap_eq_self hE₂, hsup,
    Subgroup.map_top]

theorem input14620A7 : Input14620A7 := by
  intro G _ _ K T hsyl hTK hA7
  set X : Subgroup G := K ⊔ T with hXdef
  have hKX : K ≤ X := le_sup_left
  have hTX : T ≤ X := le_sup_right
  have hQT : pCoreOf 2 X ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsyl
  have hXK : X ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTK
  have hKnorm : (K.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXK
  have hsub : IsSubnormal K X := A3.subnormal_of_normal hKX hKnorm
  set Kh : Subgroup (OTwoQuot X) := imageOTwoQuot X K with hKh
  set Th : Subgroup (OTwoQuot X) := imageOTwoQuot X T with hTh
  have hKhN : Kh.Normal := by
    refine ⟨fun u hu g => ?_⟩
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective g
    have := mk_mem_normalizer_imageOTwoQuot_of_mem z.2 (hXK z.2)
    exact (Subgroup.mem_normalizer_iff.mp this u).mp hu
  obtain ⟨eA⟩ := hA7
  obtain ⟨eI⟩ := nonempty_mulEquiv_pCore_quotient_imageOTwoQuot hsub
  let e : ↥Kh ≃* alternatingGroup (Fin 7) := (eI.symm.trans (kbarEquiv K).symm).trans eA
  have hKz : ∀ x ∈ Kh, (∀ y ∈ Kh, y * x = x * y) → x = 1 :=
    trivial_centre_of_mulEquiv e alt7_center_trivial
  have hTh2 : IsPGroup 2 ↥Th := isPGroup_imageOTwoQuot' hsyl.2.1
  have hC : ∀ y : OTwoQuot X, (∀ k ∈ Kh, y * k = k * y) → y = 1 := by
    set C : Subgroup (OTwoQuot X) := Subgroup.centralizer (Kh : Set (OTwoQuot X)) with hCdef
    have hmemC : ∀ c, c ∈ C ↔ ∀ k ∈ Kh, k * c = c * k := fun c => Subgroup.mem_centralizer_iff
    have hCn : C.Normal := by
      refine ⟨fun c hc g => ?_⟩
      rw [hmemC] at hc ⊢
      intro k hk
      have hk' : g⁻¹ * k * g ∈ Kh := by
        have := hKhN.conj_mem k hk g⁻¹
        simpa using this
      have h1 := hc _ hk'
      calc k * (g * c * g⁻¹) = g * ((g⁻¹ * k * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
        _ = (g * c * g⁻¹) * k := by group
    have hC2 : IsPGroup 2 ↥C := by
      intro c
      obtain ⟨z, hz⟩ := QuotientGroup.mk_surjective (c : OTwoQuot X)
      have hzTK : (z : G) ∈ ((T ⊔ K : Subgroup G) : Set G) := by
        rw [SetLike.mem_coe, sup_comm]
        exact z.2
      rw [Subgroup.coe_mul_of_left_le_normalizer_right T K hTK] at hzTK
      obtain ⟨t, ht, k, hk, hzt⟩ := Set.mem_mul.mp hzTK
      have htX : t ∈ X := hTX ht
      have hkX : k ∈ X := hKX hk
      have hct : (c : OTwoQuot X) =
          QuotientGroup.mk ⟨t, htX⟩ * QuotientGroup.mk ⟨k, hkX⟩ := by
        rw [← hz, ← QuotientGroup.mk_mul]
        congr 1
        exact Subtype.ext hzt.symm
      obtain ⟨b, hb⟩ := hTh2 ⟨QuotientGroup.mk ⟨t, htX⟩,
        mem_imageOTwoQuot_iff.mpr ⟨t, htX, ht, rfl⟩⟩
      refine ⟨b, ?_⟩
      have hπ : (QuotientGroup.mk' Kh : OTwoQuot X →* OTwoQuot X ⧸ Kh)
          ((c : OTwoQuot X) ^ 2 ^ b) = 1 := by
        rw [map_pow, hct, map_mul]
        have hk1 : (QuotientGroup.mk' Kh) (QuotientGroup.mk ⟨k, hkX⟩ : OTwoQuot X) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr (mem_imageOTwoQuot_iff.mpr ⟨k, hkX, hk, rfl⟩)
        rw [hk1, mul_one, ← map_pow]
        have : (QuotientGroup.mk ⟨t, htX⟩ : OTwoQuot X) ^ 2 ^ b = 1 := by
          simpa using congrArg Subtype.val hb
        rw [this, map_one]
      have hmem : (c : OTwoQuot X) ^ 2 ^ b ∈ Kh := (QuotientGroup.eq_one_iff _).mp hπ
      have hcC : (c : OTwoQuot X) ^ 2 ^ b ∈ C := Subgroup.pow_mem C c.2 _
      have h1 : (c : OTwoQuot X) ^ 2 ^ b = 1 :=
        hKz _ hmem fun y hy => (hmemC _).mp hcC y hy
      exact Subtype.ext (by simpa using h1)
    have hCle : C ≤ CFSG.Open.pCore 2 (OTwoQuot X) := le_pCore 2 hCn hC2
    have hbot : CFSG.Open.pCore 2 (OTwoQuot X) = ⊥ :=
      (CFSG.pCore_eq_open (OTwoQuot X) 2).symm.trans (pCore_two_quot_eq_bot X)
    intro y hy
    have : y ∈ C := (hmemC y).mpr fun k hk => (hy k hk).symm
    exact Subgroup.mem_bot.mp (hbot ▸ hCle this)
  obtain ⟨E₁, E₂, h1, h2, hs1, hs2, hsup⟩ := exists_two_solvable_overgroups_alt7 e hC hTh2
  refine solvGen_eq_of_quotient hTX hQT hsyl.2.1 {E₁, E₂} ?_ ?_ ?_
  · intro Y hY
    rcases hY with rfl | hY
    · exact hs1
    · rw [Set.mem_singleton_iff] at hY
      rw [hY]
      exact hs2
  · intro Y hY
    rcases hY with rfl | hY
    · exact h1
    · rw [Set.mem_singleton_iff] at hY
      rw [hY]
      exact h2
  · rw [sSup_pair, hsup]
    exact top_sup_eq _

end Alt7Main

end CFSG.Quasithin
