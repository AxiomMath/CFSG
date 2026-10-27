module

public import CFSG.Quasithin.H13.U3L134O
public import CFSG.Quasithin.H13.U3L13x8
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Aut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso
public import CFSG.Quasithin.Vol2.Ch12Sec8OneFlag
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.SectionRank.Ccomm
open scoped Pointwise

section Inn

variable {Q : Type} [Group Q]

abbrev innAut (Q : Type) [Group Q] : Subgroup (MulAut Q) := (MulAut.conj : Q →* MulAut Q).range

theorem ker_conj_eq_center : (MulAut.conj : Q →* MulAut Q).ker = center Q := by
  ext g
  rw [MonoidHom.mem_ker, mem_center_iff]
  constructor
  · intro h x
    have := congrArg (fun φ : MulAut Q => φ x) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * g = g * x * g⁻¹ * g := by rw [this]
      _ = g * x := by group
  · intro h
    ext x
    rw [MulAut.conj_apply, MulAut.one_apply, ← h x, mul_inv_cancel_right]

noncomputable def innAutEquiv (Q : Type) [Group Q] : ↥(innAut Q) ≃* Q ⧸ center Q :=
  (QuotientGroup.quotientKerEquivRange (MulAut.conj : Q →* MulAut Q)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq ker_conj_eq_center)

instance innAut_normal : (innAut Q).Normal := by
  constructor
  rintro _ ⟨g, rfl⟩ β
  refine ⟨β g, ?_⟩
  ext x
  simp only [MulAut.conj_apply, MulAut.mul_apply]
  rw [map_mul, map_mul, map_inv]
  simp

theorem center_eq_bot_of_simple [IsSimpleGroup Q] (hna : ∃ a b : Q, a * b ≠ b * a) :
    center Q = ⊥ := by
  rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    exact hab (mem_center_iff.1 (h ▸ mem_top b) a)

theorem nonabelian_of_simple [IsSimpleGroup Q] (hp : ¬ (Nat.card Q).Prime) :
    ∃ a b : Q, a * b ≠ b * a := by
  by_contra h
  push Not at h
  let _ : CommGroup Q := { (inferInstance : Group Q) with mul_comm := h }
  exact hp IsSimpleGroup.prime_card

theorem simple_of_mulEquiv {S : Type} [Group S] [IsSimpleGroup S] (e : Q ≃* S)
    (hp : ¬ (Nat.card S).Prime) : IsSimpleGroup Q ∧ ∃ a b : Q, a * b ≠ b * a := by
  have hsQ : IsSimpleGroup Q := (MulEquiv.isSimpleGroup_congr e).2 inferInstance
  refine ⟨hsQ, nonabelian_of_simple ?_⟩
  rwa [Nat.card_congr e.toEquiv]

noncomputable def quotCenterEquivOfSimple [IsSimpleGroup Q] (hna : ∃ a b : Q, a * b ≠ b * a) :
    Q ⧸ center Q ≃* Q :=
  (QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_simple hna)).trans
    QuotientGroup.quotientBot

theorem autQuotient_center_injective (hperf : Group.IsPerfect Q) :
    Function.Injective (autQuotient (center Q)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro β hβ
  rw [mem_ker_autQuotient] at hβ
  rw [mem_bot]
  let δ : Q →* center Q :=
    { toFun := fun x => ⟨x⁻¹ * β x, hβ x⟩
      map_one' := by simp
      map_mul' := fun x y => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        have hy := mem_center_iff.1 (hβ y)
        rw [map_mul]
        calc (x * y)⁻¹ * (β x * β y) = y⁻¹ * (x⁻¹ * β x) * β y := by group
          _ = (x⁻¹ * β x) * (y⁻¹ * β y) := by
            rw [(mem_center_iff.1 (hβ x)) y⁻¹]
            group }
  have hcomm : ∀ x : Q, δ x = 1 := by
    intro x
    have hx : x ∈ commutator Q := by rw [hperf.commutator_eq_top]; exact mem_top x
    have hle : commutator Q ≤ δ.ker := by
      rw [_root_.commutator_def, commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      refine commutatorElement_eq_one_iff_mul_comm.2 (Subtype.ext ?_)
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact mem_center_iff.1 (δ b).2 (δ a : Q)
    exact hle hx
  ext x
  have h1 := congrArg Subtype.val (hcomm x)
  simp only [δ, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_one] at h1
  rw [MulAut.one_apply]
  calc β x = x * (x⁻¹ * β x) := by group
    _ = x := by rw [h1, mul_one]

end Inn

section Index

variable {Q : Type} [Group Q] [Finite Q]

theorem card_mulAut_eq (Q : Type) [Group Q] [Finite Q] :
    Nat.card (MulAut Q) = (innAut Q).index * Nat.card (Q ⧸ center Q) := by
  rw [← Nat.card_congr (innAutEquiv Q).toEquiv, mul_comm]
  exact (card_mul_index (innAut Q)).symm

theorem index_innAut_of_le_two (h : Nat.card (MulAut Q) ≤ 2 * Nat.card (Q ⧸ center Q)) :
    ∃ k : ℕ, (innAut Q).index = 2 ^ k := by
  have h1 := card_mulAut_eq Q
  have hpos : 0 < Nat.card (Q ⧸ center Q) := Nat.card_pos
  have hi : (innAut Q).index ≤ 2 := by
    by_contra hc
    push Not at hc
    have : 3 * Nat.card (Q ⧸ center Q) ≤ (innAut Q).index * Nat.card (Q ⧸ center Q) :=
      Nat.mul_le_mul_right _ hc
    omega
  have hi0 : (innAut Q).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (show (innAut Q).index = 1 ∨ (innAut Q).index = 2 by omega) with hc | hc
  · exact ⟨0, by rw [hc]; rfl⟩
  · exact ⟨1, by rw [hc]; rfl⟩

theorem card_mulAut_SL32_le :
    Nat.card (MulAut (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) ≤ 336 := by
  let F : GL (Fin 3) (ZMod 2) × Bool → MulAut (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    fun p => if p.2 then
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 (ZMod 2) p.1 *
        CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 (ZMod 2)
      else CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 (ZMod 2) p.1
  have hF : Function.Surjective F := fun α => by
    rcases CFSG.QuasithinUnique.Setup.Family.aut_SL3_cases α with ⟨A, hA⟩ | ⟨A, hA⟩
    · exact ⟨(A, false), hA.symm⟩
    · exact ⟨(A, true), hA.symm⟩
  have hGL : Nat.card (GL (Fin 3) (ZMod 2)) = 168 := by
    rw [← Nat.card_congr (CFSG.QuasithinUnique.Setup.Family.slEquivGL 3).toEquiv,
      HSType.card_SL_three_two]
  calc Nat.card (MulAut (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
      ≤ Nat.card (GL (Fin 3) (ZMod 2) × Bool) := Nat.card_le_card_of_surjective F hF
    _ = 336 := by rw [Nat.card_prod, hGL, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]

theorem card_alt5 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem index_innAut_eq_two_pow
    (hQ : QT13Five Q) : ∃ k : ℕ, (innAut Q).index = 2 ^ k := by
  rcases hQ with ⟨⟨e⟩⟩ | hlin | ⟨⟨e⟩⟩ | ⟨hperf, hZ, ⟨e⟩⟩ | hU3
  ·
    have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    obtain ⟨hsQ, hna⟩ := simple_of_mulEquiv e (by rw [card_alt5]; norm_num)
    have hc : Nat.card (Q ⧸ center Q) = 60 := by
      rw [Nat.card_congr (quotCenterEquivOfSimple hna).toEquiv, Nat.card_congr e.toEquiv,
        card_alt5]
    have ha : Nat.card (MulAut Q) = 120 := by
      rw [Nat.card_congr (MulAut.congr e).toEquiv, ← Nat.card_eq_of_bijective _
        (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl
          (by norm_num)), Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      rfl
    exact index_innAut_of_le_two (by rw [ha, hc])
  ·
    obtain ⟨e⟩ := nonempty_equiv_SL32_of_lieModel hlin
    have := HSType.isSimpleGroup_SL_three_two
    obtain ⟨hsQ, hna⟩ := simple_of_mulEquiv e (by rw [HSType.card_SL_three_two]; norm_num)
    have hc : Nat.card (Q ⧸ center Q) = 168 := by
      rw [Nat.card_congr (quotCenterEquivOfSimple hna).toEquiv, Nat.card_congr e.toEquiv,
        HSType.card_SL_three_two]
    have ha : Nat.card (MulAut Q) ≤ 336 := by
      rw [Nat.card_congr (MulAut.congr e).toEquiv]
      exact card_mulAut_SL32_le
    exact index_innAut_of_le_two (by rw [hc]; omega)
  ·
    have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    obtain ⟨hsQ, hna⟩ := simple_of_mulEquiv e (by rw [card_alt6]; norm_num)
    have hc : Nat.card (Q ⧸ center Q) = 360 := by
      rw [Nat.card_congr (quotCenterEquivOfSimple hna).toEquiv, Nat.card_congr e.toEquiv]
      exact card_alt6
    have ha : Nat.card (MulAut Q) = 1440 := by
      rw [Nat.card_congr (MulAut.congr e).toEquiv]
      exact CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6
    have h1 := card_mulAut_eq Q
    rw [ha, hc] at h1
    exact ⟨2, by omega⟩
  ·
    have hc : Nat.card (Q ⧸ center Q) = 360 := by
      rw [Nat.card_congr e.toEquiv]
      exact card_alt6
    have ha : Nat.card (MulAut (Q ⧸ center Q)) = 1440 := by
      rw [Nat.card_congr (MulAut.congr e).toEquiv]
      exact CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6
    have hdvd : Nat.card (MulAut Q) ∣ 1440 := by
      rw [← ha, Nat.card_congr (MonoidHom.ofInjective
        (autQuotient_center_injective (Q := Q) hperf)).toEquiv]
      exact card_subgroup_dvd_card _
    have h1 := card_mulAut_eq Q
    rw [hc] at h1
    rw [h1] at hdvd
    have h4 : (innAut Q).index ∣ 2 ^ 2 := by
      obtain ⟨c, hc'⟩ := hdvd
      exact ⟨c, by nlinarith⟩
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h4
    exact ⟨k, hk⟩
  ·
    obtain ⟨e1⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel hU3
    obtain ⟨e2⟩ := u33Pres_mulEquiv_PSU3
    have : IsSimpleGroup U33G := isSimpleGroup_u33Pres
    obtain ⟨hsQ, hna⟩ := simple_of_mulEquiv (e1.trans e2.symm) (by rw [card_u33G]; norm_num)
    have hc : Nat.card (Q ⧸ center Q) = 6048 := by
      rw [Nat.card_congr (quotCenterEquivOfSimple hna).toEquiv,
        Nat.card_congr (e1.trans e2.symm).toEquiv]
      exact card_u33G
    have ha : Nat.card (MulAut Q) ≤ 12096 := by
      rw [Nat.card_congr (MulAut.congr (e1.trans e2.symm)).toEquiv]
      exact card_mulAut_u33Pres_le
    exact index_innAut_of_le_two (by rw [hc]; omega)

theorem sylOvergroupProp_quotCenter
    (hQ : QT13Five Q) : SylOvergroupProp (Q ⧸ center Q) := by
  have hQQ := sylOvergroupProp_of_qt13Five hQ
  rcases hQ with ⟨⟨e⟩⟩ | hlin | ⟨⟨e⟩⟩ | ⟨-, -, ⟨e⟩⟩ | hU3
  · have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    obtain ⟨hsQ, hna⟩ := simple_of_mulEquiv e (by rw [card_alt5]; norm_num)
    exact SylOvergroupProp.of_mulEquiv (quotCenterEquivOfSimple hna) hQQ
  · obtain ⟨e⟩ := nonempty_equiv_SL32_of_lieModel hlin
    have := HSType.isSimpleGroup_SL_three_two
    obtain ⟨hsQ, hna⟩ := simple_of_mulEquiv e (by rw [HSType.card_SL_three_two]; norm_num)
    exact SylOvergroupProp.of_mulEquiv (quotCenterEquivOfSimple hna) hQQ
  · have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    obtain ⟨hsQ, hna⟩ := simple_of_mulEquiv e (by rw [card_alt6]; norm_num)
    exact SylOvergroupProp.of_mulEquiv (quotCenterEquivOfSimple hna) hQQ
  · exact SylOvergroupProp.of_mulEquiv e sylOvergroupProp_alt6
  · obtain ⟨e1⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel hU3
    obtain ⟨e2⟩ := u33Pres_mulEquiv_PSU3
    have : IsSimpleGroup U33G := isSimpleGroup_u33Pres
    obtain ⟨hsQ, hna⟩ := simple_of_mulEquiv (e1.trans e2.symm) (by rw [card_u33G]; norm_num)
    exact SylOvergroupProp.of_mulEquiv (quotCenterEquivOfSimple hna) hQQ

end Index

section Act

variable {G : Type} [Group G]

@[expose] noncomputable def quotAct (K : Subgroup G) :
    ↥(normalizer (K : Set G)) →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K) :=
  (autQuotient (CFSG.pCore 2 ↥K)).comp K.normalizerMonoidHom

theorem quotAct_mk (K : Subgroup G) (n : ↥(normalizer (K : Set G))) (k : ↥K) :
    quotAct K n (QuotientGroup.mk k : ↥K ⧸ CFSG.pCore 2 ↥K) =
      QuotientGroup.mk (⟨(n : G) * k * (n : G)⁻¹, (n.2 k).mp k.2⟩ : ↥K) :=
  rfl

theorem quotAct_eq_one_iff (K : Subgroup G) (n : ↥(normalizer (K : Set G))) :
    quotAct K n = 1 ↔ (n : G) ∈ centralizerMod (pCoreOf 2 K) (normalizer (K : Set G)) K := by
  rw [mem_centralizerMod]
  have hO : (n : G) ∈ normalizer (pCoreOf 2 K : Set G) :=
    LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K n.2
  have hKO := LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have key : ∀ k : G, k ∈ K → ((k⁻¹ * ((n : G) * k * (n : G)⁻¹) ∈ pCoreOf 2 K) ↔
      ((n : G) * k * (n : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 K)) := by
    intro k hk
    have e : (n : G) * k * (n : G)⁻¹ * k⁻¹ = k * (k⁻¹ * ((n : G) * k * (n : G)⁻¹)) * k⁻¹ := by
      group
    rw [e]
    exact mem_normalizer_iff.1 (hKO hk) _
  constructor
  · intro h
    refine ⟨n.2, hO, fun k hk => (key k hk).1 ?_⟩
    have h1 := (mem_ker_autQuotient (CFSG.pCore 2 ↥K)).1
      (show K.normalizerMonoidHom n ∈ (autQuotient (CFSG.pCore 2 ↥K)).ker from h) ⟨k, hk⟩
    have h2 := (coe_mem_pCoreOf_iff (p := 2) (H := K)).2 h1
    simpa using h2
  · rintro ⟨-, -, hc⟩
    show K.normalizerMonoidHom n ∈ (autQuotient (CFSG.pCore 2 ↥K)).ker
    rw [mem_ker_autQuotient]
    intro k
    rw [← coe_mem_pCoreOf_iff (p := 2) (H := K)]
    have := (key k k.2).2 (hc k k.2)
    simpa using this

theorem quotAct_of_mem (K : Subgroup G) {k : G} (hk : k ∈ K) :
    quotAct K ⟨k, le_normalizer hk⟩ =
      MulAut.conj (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) := by
  ext x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  rw [quotAct_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
    ← QuotientGroup.mk_mul]
  rfl

end Act

theorem stmt13_3_4K_of
    (h1332 : Stmt13_3_2) : Stmt13_3_4K := by
  intro G _ _ T L K X hH hK hTX hXN hnot p hp hpX
  by_contra hne
  push Not at hne
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hQ, ⟨hTK, -, -, -⟩, -, -⟩ := h1332 G T L hH K hK
  set C := centralizerMod (pCoreOf 2 K) (normalizer (K : Set G)) K with hCdef
  set φ : ↥X →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K) := (quotAct K).comp (Subgroup.inclusion hXN)
    with hφ
  have hker : φ.ker = C.subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact quotAct_eq_one_iff K _
  have hcard : C.relIndex X = Nat.card φ.range := by
    rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  rw [hcard] at hpX
  obtain ⟨⟨β, hβ⟩, hβo⟩ := exists_prime_orderOf_dvd_card' (G := ↥φ.range) p hpX
  have hβo' : orderOf β = p := by
    rw [Subgroup.orderOf_mk] at hβo
    exact hβo
  obtain ⟨k₀, hk₀⟩ := index_innAut_eq_two_pow hQ
  have hβI : β ∈ innAut (↥K ⧸ CFSG.pCore 2 ↥K) := by
    have h1 : β ^ (innAut (↥K ⧸ CFSG.pCore 2 ↥K)).index ∈ innAut (↥K ⧸ CFSG.pCore 2 ↥K) :=
      Subgroup.pow_index_mem _ β
    rw [hk₀] at h1
    exact mem_of_pow_two_pow_mem h1 (hp.odd_of_ne_two hne.1)
      (by rw [← hβo']; exact pow_orderOf_eq_one β)
  have hsylG : IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, hH.sylow.1, ?_⟩
    show ¬ 2 ∣ T.relIndex ⊤
    rw [relIndex_top_right]
    exact hH.sylow.2
  have hTsyl : IsSylowTwoOf T (K ⊔ T) := isSylowTwoOf_of_le hsylG le_sup_right
  have hsylK : IsSylowTwoOf (T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hTsyl le_sup_left (sup_le le_normalizer hTK)
  have hP : IsPGroup 2 ((T ⊓ K).subgroupOf K) :=
    hsylK.2.1.of_equiv (subgroupOfEquivOfLe hsylK.1).symm
  let P : Sylow 2 ↥K := hP.toSylow hsylK.2.2
  let ψ : ↥K →* ↥(innAut (↥K ⧸ CFSG.pCore 2 ↥K)) :=
    ((MulAut.conj : (↥K ⧸ CFSG.pCore 2 ↥K) →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K)).comp
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).codRestrict (innAut (↥K ⧸ CFSG.pCore 2 ↥K))
      fun k => ⟨_, rfl⟩
  have hψ : Function.Surjective ψ := by
    rintro ⟨_, ⟨q, rfl⟩⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨k, rfl⟩
  set R := (φ.range ⊓ innAut (↥K ⧸ CFSG.pCore 2 ↥K)).subgroupOf
    (innAut (↥K ⧸ CFSG.pCore 2 ↥K)) with hRdef
  have hPR : ((P.mapSurjective hψ : Sylow 2 _) : Subgroup _) ≤ R := by
    rw [Sylow.coe_mapSurjective]
    rintro _ ⟨z, hz, rfl⟩
    have hzT : (z : G) ∈ T := (mem_inf.1 (mem_subgroupOf.1
      (show z ∈ (T ⊓ K).subgroupOf K from hz))).1
    rw [hRdef, mem_subgroupOf]
    refine mem_inf.2 ⟨⟨⟨z, hTX hzT⟩, ?_⟩, (ψ z).2⟩
    show quotAct K ⟨z, hXN (hTX hzT)⟩ = _
    rw [show (⟨z, hXN (hTX hzT)⟩ : ↥(normalizer (K : Set G))) = ⟨z, le_normalizer z.2⟩ from rfl,
      quotAct_of_mem]
    rfl
  have hβR : (⟨β, hβI⟩ : ↥(innAut (↥K ⧸ CFSG.pCore 2 ↥K))) ∈ R := by
    rw [hRdef, mem_subgroupOf]
    exact mem_inf.2 ⟨hβ, hβI⟩
  have hRt := SylOvergroupProp.of_mulEquiv (innAutEquiv _) (sylOvergroupProp_quotCenter hQ) R
    ⟨_, hPR⟩ p hp hne.1 hne.2 ⟨_, hβR, by rw [Subgroup.orderOf_mk, hβo']⟩
  have hIX : innAut (↥K ⧸ CFSG.pCore 2 ↥K) ≤ φ.range := by
    intro γ hγ
    have : (⟨γ, hγ⟩ : ↥(innAut (↥K ⧸ CFSG.pCore 2 ↥K))) ∈ R := hRt ▸ mem_top _
    rw [hRdef, mem_subgroupOf] at this
    exact (mem_inf.1 this).1
  set A := (quotAct K).range with hA
  have hIA : innAut (↥K ⧸ CFSG.pCore 2 ↥K) ≤ A := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨⟨k, le_normalizer k.2⟩, quotAct_of_mem K k.2⟩
  set AT := (T.subgroupOf (normalizer (K : Set G))).map (quotAct K) with hAT
  have hATX : AT ≤ φ.range := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨⟨t, hTX (mem_subgroupOf.1 ht)⟩, rfl⟩
  have hATA : AT ≤ A := by
    rintro _ ⟨t, -, rfl⟩
    exact ⟨t, rfl⟩
  have hodd : ¬ 2 ∣ AT.relIndex A := by
    intro h
    apply hH.sylow.2
    have e1 := relIndex_map_dvd (quotAct K)
      (le_top : T.subgroupOf (normalizer (K : Set G)) ≤ ⊤)
    rw [← MonoidHom.range_eq_map, relIndex_top_right] at e1
    exact h.trans (e1.trans (relIndex_dvd_index_of_le hTK))
  have hdvd1 : (AT ⊔ innAut (↥K ⧸ CFSG.pCore 2 ↥K)).relIndex A ∣ 2 ^ k₀ :=
    (relIndex_dvd_of_le_left A le_sup_right).trans
      (hk₀ ▸ relIndex_dvd_index_of_le hIA)
  have hdvd2 : (AT ⊔ innAut (↥K ⧸ CFSG.pCore 2 ↥K)).relIndex A ∣ AT.relIndex A :=
    relIndex_dvd_of_le_left A le_sup_left
  have hone : (AT ⊔ innAut (↥K ⧸ CFSG.pCore 2 ↥K)).relIndex A = 1 := by
    have hcop : Nat.Coprime (2 ^ k₀) (AT.relIndex A) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvd1 hcop) hdvd2
  have hAX : A ≤ φ.range :=
    (relIndex_eq_one.1 hone).trans (sup_le hATX hIX)
  apply hnot
  intro n hn
  obtain ⟨x, hx⟩ := hAX ⟨⟨n, hn⟩, rfl⟩
  have h1 : quotAct K ((Subgroup.inclusion hXN x)⁻¹ * ⟨n, hn⟩) = 1 := by
    rw [map_mul, map_inv]
    change (φ x)⁻¹ * quotAct K ⟨n, hn⟩ = 1
    rw [hx, inv_mul_cancel]
  have h2 := (quotAct_eq_one_iff K _).1 h1
  have e : n = (x : G) * ((x : G)⁻¹ * n) := by group
  rw [e]
  exact mul_mem_sup x.2 h2

end CFSG.Quasithin.H13.U3
