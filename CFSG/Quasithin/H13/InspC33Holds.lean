module

public import CFSG.Quasithin.Background.C31Insp
public import CFSG.Quasithin.H13.KG14726LPSL2
public import CFSG.Quasithin.EmptyFaithful.S153QPA1
public import CFSG.LieType.SteinbergBRTriangularSolvable
public import CFSG.LieType.SteinbergBRSuzukiNormalizer
public import CFSG.Quasithin.H13.NQCatC2JH
public import CFSG.Walter.J1Props.Hyp
public import CFSG.Walter.Models
public import CFSG.Walter.J1.Local
public import CFSG.CharacterTheory.Burnside
public import CFSG.GroupTheory.ABGDGroups.LinearCentralizers

public section

namespace CFSG.Quasithin.H13.InspC33P

open Subgroup CFSG.Open
open scoped commutatorElement

section Criterion

variable {Y : Type} [Group Y]

@[expose] def InspC33At (Y : Type) [Group Y] : Prop :=
  ∀ M V : Subgroup Y, ⁅M, M⁆ = M → V ≤ M → IsElemAbelian 2 V → ⁅V, M⁆ = V → V = ⊥

theorem le_normalizer_of_commutator_eq {M V : Subgroup Y} (h : ⁅V, M⁆ = V) :
    M ≤ normalizer (V : Set Y) := by
  have key : ∀ m ∈ M, ∀ v ∈ V, m * v * m⁻¹ ∈ V := by
    intro m hm v hv
    have h1 : ⁅m, v⁆ ∈ V := by
      rw [← h, commutator_comm]
      exact commutator_mem_commutator hm hv
    have h2 : m * v * m⁻¹ = ⁅m, v⁆ * v := by rw [commutatorElement_def]; group
    rw [h2]
    exact V.mul_mem h1 hv
  intro m hm
  rw [mem_normalizer_iff]
  intro v
  refine ⟨key m hm v, fun hv => ?_⟩
  have := key m⁻¹ (M.inv_mem hm) _ hv
  rwa [show m⁻¹ * (m * v * m⁻¹) * m⁻¹⁻¹ = v by group] at this

theorem eq_bot_of_solvable_autOn {M V : Subgroup Y} (hM : ⁅M, M⁆ = M) (h : ⁅V, M⁆ = V)
    (hs : Group.IsSolvable ↥(V.normalizerMonoidHom.range)) : V = ⊥ := by
  have hle := le_normalizer_of_commutator_eq h
  have : Group.IsPerfect ↥M := Subgroup.isPerfect_iff.mpr hM
  set φ : ↥M →* MulAut ↥V := V.normalizerMonoidHom.comp (inclusion hle) with hφ
  have hφr : φ.range ≤ V.normalizerMonoidHom.range := by
    rintro _ ⟨m, rfl⟩
    exact ⟨_, rfl⟩
  have : Group.IsSolvable ↥φ.range :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hφr)
  have : Group.IsPerfect ↥φ.range := Group.IsPerfect.range φ
  have hsub : Subsingleton ↥φ.range := by
    by_contra hn
    rw [not_subsingleton_iff_nontrivial] at hn
    exact Group.IsPerfect.not_isSolvable (↥φ.range) ‹_›
  have hMC : M ≤ centralizer (V : Set Y) := by
    intro m hm
    have h1 : φ ⟨m, hm⟩ = 1 := by
      have := Subsingleton.elim (⟨φ ⟨m, hm⟩, ⟨_, rfl⟩⟩ : ↥φ.range) 1
      exact congrArg Subtype.val this
    have h2 : (inclusion hle ⟨m, hm⟩ : ↥(normalizer (V : Set Y))) ∈
        V.normalizerMonoidHom.ker := h1
    rw [normalizerMonoidHom_ker, mem_subgroupOf] at h2
    exact h2
  have h0 : ⁅V, M⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hMC
  rw [← h, h0]

theorem eq_bot_of_solvable_normalizer {M V : Subgroup Y} (hM : ⁅M, M⁆ = M) (h : ⁅V, M⁆ = V)
    (hs : Group.IsSolvable ↥(normalizer (V : Set Y))) : V = ⊥ :=
  eq_bot_of_solvable_autOn hM h
    (Group.isSolvable_of_surjective V.normalizerMonoidHom.rangeRestrict_surjective)

theorem eq_bot_of_card_le_four [Finite Y] {M V : Subgroup Y} (hM : ⁅M, M⁆ = M)
    (h : ⁅V, M⁆ = V) (hV : Nat.card V ≤ 4) : V = ⊥ := by
  have : Group.IsSolvable (Equiv.Perm ↥V) := Equiv.Perm.isSolvable hV
  have : Group.IsSolvable (MulAut ↥V) :=
    Group.isSolvable_of_isSolvable_injective (f := MulAut.toPerm ↥V)
      fun a b hab => MulEquiv.toEquiv_injective hab
  exact eq_bot_of_solvable_autOn hM h
    (Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _))

theorem inspC33At_of_mulEquiv {Y' : Type} [Group Y'] (e : Y ≃* Y') (h : InspC33At Y') :
    InspC33At Y := by
  intro M V hM hVM hV hc
  have hVe : IsElemAbelian 2 (V.map e.toMonoidHom) := by
    obtain ⟨hcomm, hp⟩ := hV
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, x, hx, rfl⟩ := a
      obtain ⟨_, y, hy, rfl⟩ := b
      apply Subtype.ext
      have := congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      simp only [coe_mul] at this ⊢
      rw [← map_mul, ← map_mul, this]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hp x hx, map_one]
  have h1 := h (M.map e.toMonoidHom) (V.map e.toMonoidHom) (by rw [← map_commutator, hM])
    (map_mono hVM) hVe (by rw [← map_commutator, hc])
  exact (map_eq_bot_iff_of_injective _ e.injective).mp h1

end Criterion

theorem card_le_four_of_dihedral {m : ℕ} [NeZero m] {E : Subgroup (DihedralGroup m)}
    (hE : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 4 := by
  set C := zpowers (DihedralGroup.r (1 : ZMod m)) with hCdef
  have hCi : C.index = 2 := by
    have h1 := C.card_mul_index
    rw [hCdef, Nat.card_zpowers, DihedralGroup.orderOf_r_one, Nat.card_eq_fintype_card,
      DihedralGroup.card] at h1
    have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    nlinarith
  have : C.Normal := Subgroup.normal_of_index_eq_two hCi
  have h1 := Subgroup.relIndex_mul_card C E
  have h2 : C.relIndex E ≤ 2 := by
    have := relIndex_dvd_index_of_normal C E
    rw [hCi] at this
    exact Nat.le_of_dvd (by norm_num) this
  have h3 : Nat.card ↥(C ⊓ E) ≤ 2 := by
    set D := (C ⊓ E).subgroupOf C with hD
    have hDcard : Nat.card D = Nat.card ↥(C ⊓ E) :=
      Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥D)
    have hg2 : g ^ 2 = 1 := by
      have hgE : (((g : ↥C) : DihedralGroup m)) ∈ E := (mem_subgroupOf.mp g.2).2
      apply Subtype.ext
      apply Subtype.ext
      simp only [pow_two, coe_mul, OneMemClass.coe_one]
      exact hE _ hgE
    rw [← hDcard, ← orderOf_eq_card_of_forall_mem_zpowers hg]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg2)
  rw [← h1]
  nlinarith

theorem inspC33At_psl2_p {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (h : IsPSL 2 p 1 Y) : InspC33At Y := by
  obtain ⟨-, K, _, _, hK, ⟨eT⟩⟩ := h
  rw [pow_one] at hK
  let e : Y ≃* CFSG.GorensteinWalter.PSL2 K :=
    eT.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  refine inspC33At_of_mulEquiv e ?_
  intro M V hM _ hV hc
  refine eq_bot_of_card_le_four hM hc ?_
  by_cases hV1 : V = ⊥
  · rw [hV1, Subgroup.card_bot]
    norm_num
  obtain ⟨⟨t, htV⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hV1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : orderOf t = 2 :=
    orderOf_eq_prime (hV.2 t htV) (fun h1 => ht1 (Subtype.ext h1))
  have hpo : Odd p := hp.odd_of_ne_two (by omega)
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K) :=
    ⟨p, 1, hp, hpo, le_rfl, by rw [hK, pow_one]⟩
  obtain ⟨ε, hε, hε1⟩ : ∃ ε : ℤ, (Nat.card K : ℤ) ≡ ε [ZMOD 4] ∧ (ε = 1 ∨ ε = -1) := by
    obtain ⟨r, hr⟩ := hpo
    rcases Nat.even_or_odd r with ⟨s, hs⟩ | ⟨s, hs⟩
    · refine ⟨1, ?_, Or.inl rfl⟩
      rw [hK, hr, hs, Int.ModEq]
      push_cast
      omega
    · refine ⟨-1, ?_, Or.inr rfl⟩
      rw [hK, hr, hs, Int.ModEq]
      push_cast
      omega
  obtain ⟨m, hm, ⟨eD⟩⟩ := CFSG.ABGDGroups.psl2_centralizer_involution_dihedral hodd hε hε1 ht2
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [hK] at hm
    rcases hε1 with rfl | rfl <;> push_cast at hm <;> omega
  have : NeZero m := ⟨hm0⟩
  have hVC : V ≤ centralizer ({t} : Set (CFSG.GorensteinWalter.PSL2 K)) := by
    intro v hv
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hV.1.is_comm.comm ⟨v, hv⟩ ⟨t, htV⟩)
  set E := (V.subgroupOf (centralizer ({t} : Set (CFSG.GorensteinWalter.PSL2 K)))).map
    eD.toMonoidHom with hEdef
  have hE : ∀ x ∈ E, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul]
    have hx2 : x * x = 1 := by
      apply Subtype.ext
      rw [coe_mul, ← pow_two]
      exact hV.2 _ (mem_subgroupOf.mp hx)
    rw [hx2, map_one]
  have hcard : Nat.card E = Nat.card V := by
    rw [hEdef, card_map_of_injective eD.injective]
    exact Nat.card_congr (subgroupOfEquivOfLe hVC).toEquiv
  rw [← hcard]
  exact card_le_four_of_dihedral hE

section SL2

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem isSolvable_normalizer_sl2 {n : ℕ} (hF : Nat.card F = 2 ^ n)
    {V : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)} (hV : IsElemAbelian 2 V) (hV1 : V ≠ ⊥) :
    Group.IsSolvable ↥(normalizer (V : Set (Matrix.SpecialLinearGroup (Fin 2) F))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨t, htV⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hV1
  have ht1' : t ≠ 1 := fun h1 => ht1 (Subtype.ext h1)
  have hVp : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by rw [pow_one]; exact hV.2 x x.2)⟩
  obtain ⟨S, hVS⟩ := hVp.exists_le_sylow
  have hSp : IsPGroup 2 (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) := S.isPGroup'
  have hSexp : ∀ s ∈ (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)), s * s = 1 := by
    have : Nontrivial ↥(S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) :=
      ⟨⟨⟨t, hVS htV⟩, 1, fun h1 => ht1' (congrArg Subtype.val h1)⟩⟩
    have := hSp.center_nontrivial
    obtain ⟨z₀, hz₀⟩ := exists_ne
      (1 : ↥(center ↥(S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))))
    obtain ⟨k, hk⟩ := hSp ((z₀ : ↥(S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))))
    have hz₀1 : ((z₀ : ↥(S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))) :
        Matrix.SpecialLinearGroup (Fin 2) F) ≠ 1 := by
      intro h1
      apply hz₀
      apply Subtype.ext
      exact Subtype.ext h1
    set w : Matrix.SpecialLinearGroup (Fin 2) F :=
      ((z₀ : ↥(S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))) :
        Matrix.SpecialLinearGroup (Fin 2) F) with hw
    have hwk : w ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa [hw] using this
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hwk)
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hj
      exact hz₀1 hj
    have h2w : 2 ∣ orderOf w := by
      rw [hj]
      exact dvd_pow_self 2 hj0
    set u := w ^ (orderOf w / 2) with hu
    have hu2 : orderOf u = 2 := orderOf_pow_orderOf_div (orderOf_pos w).ne' h2w
    have huu : u * u = 1 := by
      have := pow_orderOf_eq_one u
      rw [hu2, pow_two] at this
      exact this
    have hu1 : u ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hu2
      exact absurd hu2 (by norm_num)
    intro s hs
    refine CFSG.Quasithin.H13.KG14726.mul_self_eq_one_of_commute_sl2 huu hu1 ?_
    have hc := mem_center_iff.mp z₀.2 ⟨s, hs⟩
    have hc' : s * w = w * s := congrArg Subtype.val hc
    exact (Commute.pow_right (hc' : Commute s w) _).eq
  have hScomm : ∀ a ∈ (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)),
      ∀ b ∈ (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)), a * b = b * a := by
    intro a ha b hb
    have hab := hSexp _ (mul_mem ha hb)
    have ha' := hSexp a ha
    have hb' := hSexp b hb
    calc a * b = a * b * (b * a) * (b * a) := by
          rw [mul_assoc (a * b), hSexp _ (mul_mem hb ha), mul_one]
      _ = a * (b * b) * a * (b * a) := by group
      _ = b * a := by rw [hb', mul_one, ha', one_mul]
  have hCS : ∀ u ∈ (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)), u ≠ 1 →
      ∀ y : Matrix.SpecialLinearGroup (Fin 2) F,
        y ∈ (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) ↔ y * u = u * y := by
    intro u huS hu1 y
    have huu := hSexp u huS
    have hC2 : IsPGroup 2 (centralizer ({u} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) :=
      fun x => ⟨1, Subtype.ext (by
        rw [pow_one, coe_pow, pow_two]
        exact CFSG.Quasithin.H13.KG14726.mul_self_eq_one_of_commute_sl2 huu hu1
          (mem_centralizer_singleton_iff.mp x.2))⟩
    have hSC : (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) ≤
        centralizer ({u} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) :=
      fun s hs => mem_centralizer_singleton_iff.mpr (hScomm s hs u huS)
    have heq := S.is_maximal' hC2 hSC
    rw [← mem_centralizer_singleton_iff, heq]
  have hNV : normalizer (V : Set (Matrix.SpecialLinearGroup (Fin 2) F)) ≤
      normalizer ((S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) :
        Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro y
    have hgt : g * t * g⁻¹ ∈ V := (mem_normalizer_iff.mp hg t).mp htV
    have hgt1 : g * t * g⁻¹ ≠ 1 := by
      intro h1
      apply ht1'
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    rw [hCS t (hVS htV) ht1' y, hCS _ (hVS hgt) hgt1 (g * y * g⁻¹)]
    constructor
    · intro h1
      calc g * y * g⁻¹ * (g * t * g⁻¹) = g * (y * t) * g⁻¹ := by group
        _ = g * (t * y) * g⁻¹ := by rw [h1]
        _ = g * t * g⁻¹ * (g * y * g⁻¹) := by group
    · intro h1
      calc y * t = g⁻¹ * (g * y * g⁻¹ * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * t * g⁻¹ * (g * y * g⁻¹)) * g := by rw [h1]
        _ = t * y := by group
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf
      (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) ⊤ := by
    refine ⟨le_top, hSp, ?_⟩
    rw [show ((S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).subgroupOf ⊤).index =
      (S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).index from
      Subgroup.relIndex_top_right _]
    exact S.not_dvd_index
  obtain ⟨g, hg⟩ := CFSG.Quasithin.QP.exists_conj_normalizer_of_isSylowTwoOf (n := 2)
    (by norm_num) hSyl
  have hB := CFSG.LieType.SteinbergBR.isSolvable_upperTriangular_of_card Nat.prime_two hF 2
  have hNS : Group.IsSolvable ↥(normalizer ((S : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) :
      Set (Matrix.SpecialLinearGroup (Fin 2) F))) := by
    rw [hg]
    exact Group.isSolvable_of_surjective
      (f := ((CFSG.LocalAnalysis.ComponentInitial.LinearFlag.upperTriangular 2
        F).equivMapOfInjective _ (MulAut.conj g).injective).toMonoidHom) (MulEquiv.surjective _)
  exact Group.isSolvable_of_isSolvable_injective (inclusion_injective hNV)

end SL2

theorem inspC33At_psl2_two {Y : Type} [Group Y] [Finite Y] {n : ℕ} (h : IsPSL 2 2 n Y) :
    InspC33At Y := by
  obtain ⟨⟨-, hn1, -, -, -⟩, K, _, _, hK, ⟨eT⟩⟩ := h
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK
  have hc : center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center,
      CFSG.Quasithin.H13.KG14726.scalars_two_eq_bot]
  let e : Y ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    (eT.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).trans
      ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot)
  refine inspC33At_of_mulEquiv e ?_
  intro M V hM _ hV hc'
  by_cases hV1 : V = ⊥
  · exact hV1
  exact eq_bot_of_solvable_normalizer hM hc' (isSolvable_normalizer_sl2 hK hV hV1)

theorem inspC33At_sz {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : IsSz n Y) : InspC33At Y := by
  obtain ⟨-, a, -, K, _, _, hn, hK, ⟨e⟩⟩ := h
  refine inspC33At_of_mulEquiv e ?_
  intro M V hM _ hV hc
  by_cases hV1 : V = ⊥
  · exact hV1
  have hVp : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by rw [pow_one]; exact hV.2 x x.2)⟩
  exact eq_bot_of_solvable_normalizer hM hc
    (CFSG.LieType.suzuki_nontrivial_two_subgroup_normalizer_solvable (hn ▸ hK) V hVp hV1).2

theorem inspC33At_J1 {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* CFSG.Blueprint.NativeSporadic.Carrier .J1) : InspC33At Y := by
  have hJ : CFSG.Walter.J1.JankoHyp Y :=
    CFSG.Quasithin.H13.NQCat.C2.jankoHypOfMulEquiv CFSG.Walter.J1Props.jankoHyp
      (e.trans CFSG.Walter.walterJ1EquivNative.symm)
  intro M V hM _ hV hc
  by_cases h4 : Nat.card V ≤ 4
  · exact eq_bot_of_card_le_four hM hc h4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVp : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by rw [pow_one]; exact hV.2 x x.2)⟩
  obtain ⟨S, hVS⟩ := hVp.exists_le_sylow
  obtain ⟨hS8, -, hScomm, -⟩ := hJ.sylow_structure S
  have hVeq : V = (S : Subgroup Y) := by
    have hdvd : Nat.card V ∣ 8 := hS8 ▸ card_dvd_of_le hVS
    have h8 : Nat.card V = 8 := by
      have : Nat.card V ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases h : Nat.card V <;> simp_all
    exact eq_of_le_of_card_ge hVS (by rw [hS8, h8])
  refine eq_bot_of_solvable_normalizer hM hc ?_
  rw [hVeq]
  obtain ⟨h21, -⟩ := hJ.normalizer_quotient S
  set N := normalizer ((S : Subgroup Y) : Set Y) with hN
  have : ((S : Subgroup Y).subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have : Group.IsSolvable ↥((S : Subgroup Y).subgroupOf N) := by
    refine Group.isSolvable_of_comm fun a b => Subtype.ext (Subtype.ext ?_)
    exact hScomm _ (mem_subgroupOf.mp a.2) _ (mem_subgroupOf.mp b.2)
  have : Group.IsSolvable (↥N ⧸ (S : Subgroup Y).subgroupOf N) := by
    have := Fintype.ofFinite (↥N ⧸ (S : Subgroup Y).subgroupOf N)
    refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      (p := 3) (q := 7) (a := 1) (b := 1) Nat.prime_three (by norm_num) (by norm_num) ?_
    rw [← Nat.card_eq_fintype_card, h21]
    norm_num
  exact Group.isSolvable_of_subgroup_quotient ((S : Subgroup Y).subgroupOf N)

theorem inspC33_holds :
    CFSG.Quasithin.InspC33 := by
  intro Y _ _ hY
  rcases hY with ⟨n, h⟩ | ⟨n, h⟩ | hJ | ⟨p, hp, hp3, h⟩
  · exact inspC33At_psl2_two h
  · exact inspC33At_sz h
  · obtain ⟨e⟩ := hJ
    exact inspC33At_J1 e
  · exact inspC33At_psl2_p hp hp3 h

end CFSG.Quasithin.H13.InspC33P

end
