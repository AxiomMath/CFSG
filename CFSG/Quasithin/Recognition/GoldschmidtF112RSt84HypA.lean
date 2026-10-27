module

public import CFSG.Quasithin.Background.F1Cartan
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112SliceTypes

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G]

theorem index_normalizer_psl2 {f : ℕ} (hf : f ≠ 0)
    {T : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f))}
    (hp : IsPGroup 2 T) (hodd : ¬ 2 ∣ T.index) :
    (Subgroup.normalizer (T : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)))).index
      = 2 ^ f + 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P := hp.toSylow hodd
  have hP : (P : Subgroup _) = T := rfl
  have h := P.card_eq_index_normalizer
  rw [CFSG.Walter.psl2_even_card_sylow hf] at h
  rw [← hP]
  exact h.symm

theorem index_borelOf_of_psl2 {L S : Subgroup G} {f : ℕ} (hf : f ≠ 0)
    (hsyl : IsSylowTwoOf (S ⊓ L) L) (e : IsL2Quot f (oTwoQuot ↥L)) :
    ((borelOf L S).subgroupOf L).index = 2 ^ f + 1 := by
  obtain ⟨e⟩ := e
  obtain ⟨hp, hodd, hmap⟩ := F1.map_borelOf_eq_normalizer hsyl
  set π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L) with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ (borelOf L S).subgroupOf L := by
    rw [hπ, QuotientGroup.ker_mk']
    intro x hx
    have h1 : (x : G) ∈ pCoreOf 2 L := (F1.mem_pCore_iff_coe x).mp hx
    exact F1.sylow_le_borelOf L S (isSylowTwoOf_pCoreOf_le hsyl h1)
  rw [← Subgroup.index_map_eq _ hsurj hker, hmap]
  set Tb : Subgroup (oTwoQuot ↥L) := Subgroup.map π ((S ⊓ L).subgroupOf L) with hTb
  have hT' : IsPGroup 2 (Tb.map e.toMonoidHom) := hp.map e.toMonoidHom
  have hodd' : ¬ 2 ∣ (Tb.map e.toMonoidHom).index := by
    rw [show e.toMonoidHom = (e : oTwoQuot ↥L →* _) from rfl, Subgroup.index_map_equiv]
    exact hodd
  have h5 := index_normalizer_psl2 hf hT' hodd'
  rw [← Subgroup.map_normalizer_eq_of_bijective Tb e.bijective,
    show e.toMonoidHom = (e : oTwoQuot ↥L →* _) from rfl, Subgroup.index_map_equiv] at h5
  exact h5

theorem eq_bot_of_normal_le_normalizer_psl2 {f : ℕ} (hf : f ≠ 0)
    {T K : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f))}
    (hp : IsPGroup 2 T) (hodd : ¬ 2 ∣ T.index) (hK : K.Normal)
    (hle : K ≤ Subgroup.normalizer (T : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
      (GaloisField 2 f)))) : K = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx := index_normalizer_psl2 hf hp hodd
  rcases Nat.lt_or_ge f 2 with h1 | h2
  ·
    have hf1 : f = 1 := by omega
    subst hf1
    let P := hp.toSylow hodd
    have hP : (P : Subgroup _) = T := rfl
    have hN : Nat.card (Subgroup.normalizer
        ((P : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 1))) :
          Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 1)))) = 2 := by
      have := CFSG.Walter.psl2_even_card_normalizer_sylow_two (f := 1) one_ne_zero P
      simpa using this
    rw [← hP] at hle
    have hdvd : Nat.card K ∣ 2 := by
      have := Subgroup.card_dvd_of_le hle
      rwa [hN] at this
    have hG : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 1)) = 6 := by
      have := CFSG.Walter.psl2_even_card (f := 1) one_ne_zero
      simpa using this
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hc | hc
    · exact Subgroup.eq_bot_of_card_eq K hc
    · exfalso
      have hKp : IsPGroup 2 K := IsPGroup.of_card (n := 1) (by simpa using hc)
      have hKidx : K.index = 3 := by
        have := K.index_mul_card
        rw [hc, hG] at this
        omega
      have hKodd : ¬ 2 ∣ K.index := by rw [hKidx]; decide
      let Q := hKp.toSylow hKodd
      have hQK : (Q : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 1))) = K :=
        rfl
      have hQn : (Q : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 1))).Normal := by
        rw [hQK]; exact hK
      haveI := Sylow.unique_of_normal Q hQn
      have h3 := CFSG.Walter.psl2_even_card_sylow (f := 1) one_ne_zero
      have : Nat.card (Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 1))) = 1 :=
        Nat.card_unique
      omega
  ·
    have hE4 : 4 ≤ Nat.card (GaloisField 2 f) := by
      rw [GaloisField.card 2 f hf]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h2
    haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hE4
    rcases hK.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      rw [h, top_le_iff] at hle
      rw [hle, Subgroup.index_top] at hidx
      have : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      omega

theorem le_pCore_of_normal_le_borelOf {L S : Subgroup G} {f : ℕ} (hf : f ≠ 0)
    (hsyl : IsSylowTwoOf (S ⊓ L) L) (e : IsL2Quot f (oTwoQuot ↥L)) {K : Subgroup ↥L}
    (hK : K.Normal) (hle : K ≤ (borelOf L S).subgroupOf L) : K ≤ CFSG.Open.pCore 2 ↥L := by
  obtain ⟨e⟩ := e
  obtain ⟨hp, hodd, hmap⟩ := F1.map_borelOf_eq_normalizer hsyl
  set π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L) with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Tb : Subgroup (oTwoQuot ↥L) := Subgroup.map π ((S ⊓ L).subgroupOf L) with hTb
  have hKn : ((K.map π).map e.toMonoidHom).Normal :=
    (hK.map π hsurj).map e.toMonoidHom e.surjective
  have hKle : (K.map π).map e.toMonoidHom ≤
      Subgroup.normalizer ((Tb.map e.toMonoidHom : Subgroup _) : Set _) := by
    rw [← Subgroup.map_normalizer_eq_of_bijective Tb e.bijective]
    exact Subgroup.map_mono (hmap ▸ Subgroup.map_mono hle)
  have hp' : IsPGroup 2 (Tb.map e.toMonoidHom) := hp.map e.toMonoidHom
  have hodd' : ¬ 2 ∣ (Tb.map e.toMonoidHom).index := by
    rw [show e.toMonoidHom = (e : oTwoQuot ↥L →* _) from rfl, Subgroup.index_map_equiv]
    exact hodd
  have hbot := eq_bot_of_normal_le_normalizer_psl2 hf hp' hodd' hKn hKle
  have hbot' : K.map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff_of_injective _ e.injective] at hbot
    exact hbot
  rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at hbot'
  exact hbot'

theorem exists_levi_hom {L P B : Subgroup G} {X : Type*} [Group X] (hLP : L ≤ P)
    (hLR : L ⊓ coreIn B P = pCoreOf 2 L) (e : oTwoQuot ↥L ≃* X) :
    ∃ φ : ↥(⁅L, L⁆ ⊔ coreIn B P) →* ↥(commutator X), Function.Surjective φ ∧
      φ.ker = (coreIn B P).subgroupOf (⁅L, L⁆ ⊔ coreIn B P) := by
  set R := coreIn B P with hRdef
  have hRP : R ≤ P := coreIn_le_left B P
  haveI hRn : (R.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRP).mpr (le_normalizer_coreIn B P)
  set Q := ↥P ⧸ R.subgroupOf P
  let q : ↥P →* Q := QuotientGroup.mk' _
  let ρ : ↥L →* Q := q.comp (Subgroup.inclusion hLP)
  have hmemR : ∀ x : ↥P, q x = 1 ↔ (x : G) ∈ R := by
    intro x
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hkerρ : ρ.ker = CFSG.Open.pCore 2 ↥L := by
    ext x
    rw [MonoidHom.mem_ker, F1.mem_pCore_iff_coe, ← hLR]
    simp only [ρ, MonoidHom.coe_comp, Function.comp_apply]
    rw [hmemR]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  let ψ : ↥L →* X := e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L))
  have hψsurj : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let χ : ↥ρ.range ≃* X := (QuotientGroup.quotientKerEquivRange ρ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hkerρ).trans e)
  have hχ : ∀ l : ↥L, χ (ρ.rangeRestrict l) = ψ l := by
    intro l
    have h1 : (QuotientGroup.quotientKerEquivRange ρ).symm (ρ.rangeRestrict l) =
        (QuotientGroup.mk l : ↥L ⧸ ρ.ker) := by
      rw [MulEquiv.symm_apply_eq]; rfl
    simp only [χ, MulEquiv.trans_apply, h1]
    rfl
  have hKL : ⁅L, L⁆ ≤ L := Subgroup.commutator_le_self L
  have hNP : ⁅L, L⁆ ⊔ R ≤ P := sup_le (hKL.trans hLP) hRP
  have hKN : ⁅L, L⁆ ≤ ⁅L, L⁆ ⊔ R := le_sup_left
  have hRN : R ≤ ⁅L, L⁆ ⊔ R := le_sup_right
  have hN : ∀ n : ↥(⁅L, L⁆ ⊔ R), q (Subgroup.inclusion hNP n) ∈ ρ.range := by
    let Z : Subgroup G := (ρ.range.comap q).map P.subtype
    have hLZ : L ≤ Z := fun x hx => ⟨⟨x, hLP hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
    have hRZ : R ≤ Z := fun x hx => ⟨⟨x, hRP hx⟩, by
      show q ⟨x, hRP hx⟩ ∈ ρ.range
      rw [(hmemR _).mpr hx]; exact ρ.range.one_mem, rfl⟩
    intro n
    obtain ⟨y, hy, hyn⟩ := sup_le (hKL.trans hLZ) hRZ n.2
    have : y = Subgroup.inclusion hNP n := Subtype.ext hyn
    rw [← this]; exact hy
  let φ1 : ↥(⁅L, L⁆ ⊔ R) →* ↥ρ.range :=
    (q.comp (Subgroup.inclusion hNP)).codRestrict ρ.range hN
  let φ2 : ↥(⁅L, L⁆ ⊔ R) →* X := χ.toMonoidHom.comp φ1
  have hcomm : (commutator ↥L).map ψ = commutator X := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hψsurj, commutator_def]
  have hφ2L : ∀ (n : ↥(⁅L, L⁆ ⊔ R)) (l : ↥L), (n : G) = l → φ2 n = ψ l := by
    intro n l hnl
    rw [← hχ l]
    simp only [φ2, φ1, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    congr 1
    apply Subtype.ext
    simp only [MonoidHom.codRestrict_apply, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.coe_rangeRestrict, ρ]
    congr 1
    exact Subtype.ext hnl
  have hW : ∀ n : ↥(⁅L, L⁆ ⊔ R), φ2 n ∈ commutator X := by
    let W : Subgroup G := ((((commutator X).comap χ.toMonoidHom).comap φ1).map
      (⁅L, L⁆ ⊔ R).subtype)
    have hKW : ⁅L, L⁆ ≤ W := by
      intro x hx
      have hx' := hx
      rw [← Subgroup.map_subtype_commutator] at hx'
      obtain ⟨l, hl, rfl⟩ := hx'
      refine ⟨⟨l, hKN hx⟩, ?_, rfl⟩
      show φ2 _ ∈ commutator X
      rw [hφ2L _ l rfl, ← hcomm]
      exact Subgroup.mem_map_of_mem ψ hl
    have hRW : R ≤ W := by
      intro x hx
      refine ⟨⟨x, hRN hx⟩, ?_, rfl⟩
      show φ2 _ ∈ commutator X
      have : φ1 ⟨x, hRN hx⟩ = 1 := by
        apply Subtype.ext
        exact (hmemR _).mpr hx
      simp only [φ2, MonoidHom.coe_comp, Function.comp_apply, this, map_one]
      exact (commutator X).one_mem
    intro n
    obtain ⟨y, hy, hyn⟩ := sup_le hKW hRW n.2
    have : y = n := Subtype.ext hyn
    rw [← this]; exact hy
  refine ⟨φ2.codRestrict (commutator X) hW, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    rw [← hcomm] at hy
    obtain ⟨l, hl, rfl⟩ := hy
    have hlK : (l : G) ∈ ⁅L, L⁆ := by
      rw [← Subgroup.map_subtype_commutator]; exact Subgroup.mem_map_of_mem _ hl
    refine ⟨⟨l, hKN hlK⟩, ?_⟩
    apply Subtype.ext
    exact hφ2L _ l rfl
  · ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : φ2 n = 1 := congrArg Subtype.val h
      have h2 : φ1 n = 1 := by
        simpa [φ2] using h1
      have h3 : q (Subgroup.inclusion hNP n) = 1 := congrArg Subtype.val h2
      exact (hmemR _).mp h3
    · intro h
      apply Subtype.ext
      have h2 : φ1 n = 1 := Subtype.ext ((hmemR _).mpr h)
      show φ2 n = 1
      simp only [φ2, MonoidHom.coe_comp, Function.comp_apply, h2, map_one]

theorem mem_normalizer_of_conj {H : Subgroup G} {g : G} (h1 : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (h2 : ∀ x ∈ H, g⁻¹ * x * g ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  simpa [mul_assoc] using this

theorem le_normalizer_sup {A C P : Subgroup G} (hA : P ≤ Subgroup.normalizer (A : Set G))
    (hC : P ≤ Subgroup.normalizer (C : Set G)) : P ≤ Subgroup.normalizer ((A ⊔ C : Subgroup G) : Set G) := by
  have key : ∀ g ∈ P, ∀ x ∈ A ⊔ C, g * x * g⁻¹ ∈ A ⊔ C := by
    intro g hg
    have hle : A ⊔ C ≤ (A ⊔ C).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact (le_sup_left : A ≤ A ⊔ C) (((Subgroup.mem_normalizer_iff.mp (hA hg)) x).mp hx)
      · exact (le_sup_right : C ≤ A ⊔ C) (((Subgroup.mem_normalizer_iff.mp (hC hg)) x).mp hx)
    intro x hx
    exact hle hx
  intro g hg
  refine mem_normalizer_of_conj (key g hg) (fun x hx => ?_)
  simpa using key g⁻¹ (P.inv_mem hg) x hx

theorem le_normalizer_inf {A C P : Subgroup G} (hA : P ≤ Subgroup.normalizer (A : Set G))
    (hC : P ≤ Subgroup.normalizer (C : Set G)) : P ≤ Subgroup.normalizer ((A ⊓ C : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, (Subgroup.mem_normalizer_iff.mp (hA hg)) x,
    (Subgroup.mem_normalizer_iff.mp (hC hg)) x]

theorem normalizer_le_normalizer_commutator (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer ((⁅L, L⁆ : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (L : Set G), ∀ x ∈ ⁅L, L⁆, g * x * g⁻¹ ∈ ⁅L, L⁆ := by
    intro g hg
    have hle : ⁅L, L⁆ ≤ (⁅L, L⁆ : Subgroup G).comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_comap]
      have ha' := ((Subgroup.mem_normalizer_iff.mp hg) a).mp ha
      have hb' := ((Subgroup.mem_normalizer_iff.mp hg) b).mp hb
      have hc := Subgroup.commutator_mem_commutator ha' hb'
      convert hc using 1
      simp only [MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        commutatorElement_def]
      group
    intro x hx
    exact hle hx
  intro g hg
  refine mem_normalizer_of_conj (key g hg) (fun x hx => ?_)
  simpa using key g⁻¹ (Subgroup.inv_mem _ hg) x hx

@[expose] def St84Levi (M D : Subgroup G) (n : ℕ) : Prop :=
  ∃ N : Subgroup G, N ≤ M ∧ M ≤ Subgroup.normalizer (N : Set G) ∧ coreIn D M ≤ N ∧
    ∃ φ : ↥N →* ↥(commutator (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n))),
      Function.Surjective φ ∧ φ.ker = (coreIn D M).subgroupOf N

structure St84HypA (M1 M2 : Subgroup G) (n1 n2 : ℕ) : Prop where
  core : coreIn (M1 ⊓ M2) (M1 ⊔ M2) = ⊥
  index_left : (M1 ⊓ M2).relIndex M1 = 2 ^ n1 + 1
  index_right : (M1 ⊓ M2).relIndex M2 = 2 ^ n2 + 1
  one_le_left : 1 ≤ n1
  one_le_right : 1 ≤ n2
  one_lt_max : 1 < max n1 n2
  levi_left : St84Levi M1 (M1 ⊓ M2) n1
  levi_right : St84Levi M2 (M1 ⊓ M2) n2

theorem st84Levi_of_vertex {L P B S : Subgroup G} {n : ℕ} (hn : n ≠ 0)
    (hsyl : IsSylowTwoOf (S ⊓ L) L) (e : IsL2Quot n (oTwoQuot ↥L)) (hLP : L ≤ P)
    (hPL : P ≤ Subgroup.normalizer (L : Set G)) (hLB : L ⊓ B = borelOf L S) :
    St84Levi P B n := by
  set R := coreIn B P with hRdef
  have hRP : R ≤ P := coreIn_le_left B P
  have hPR : P ≤ Subgroup.normalizer (R : Set G) := le_normalizer_coreIn B P
  have hBorB : borelOf L S ≤ B := by rw [← hLB]; exact inf_le_right
  have hO : pCoreOf 2 L ≤ borelOf L S := fun x hx =>
    F1.sylow_le_borelOf L S (isSylowTwoOf_pCoreOf_le hsyl hx)
  have hOL : pCoreOf 2 L ≤ L := Subgroup.map_subtype_le _
  have hLR : L ⊓ R = pCoreOf 2 L := by
    apply le_antisymm
    · let K : Subgroup ↥L := (L ⊓ R).subgroupOf L
      have hKn : K.Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
          (le_normalizer_inf Subgroup.le_normalizer (hLP.trans hPR))
      have hKB : K ≤ (borelOf L S).subgroupOf L := by
        intro x hx
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        rw [← hLB]
        exact ⟨hx.1, coreIn_le_right B P hx.2⟩
      have hK := le_pCore_of_normal_le_borelOf hn hsyl e hKn hKB
      intro x hx
      have hx' : (⟨x, hx.1⟩ : ↥L) ∈ K := by rw [Subgroup.mem_subgroupOf]; exact hx
      exact (F1.mem_pCore_iff_coe _).mp (hK hx')
    · refine le_inf hOL (le_coreIn (hOL.trans hLP) ?_ (hO.trans hBorB))
      exact hPL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  obtain ⟨e⟩ := e
  obtain ⟨φ, hs, hk⟩ := exists_levi_hom (B := B) hLP hLR e
  exact ⟨⁅L, L⁆ ⊔ R, sup_le ((Subgroup.commutator_le_self L).trans hLP) hRP,
    le_normalizer_sup (hPL.trans (normalizer_le_normalizer_commutator L)) hPR, le_sup_right,
    φ, hs, hk⟩

theorem isL2Quot_of_VS3 {L : Subgroup G} (h : VS3 L) : IsL2Quot 1 (oTwoQuot ↥L) := by
  obtain ⟨e⟩ := h
  exact ⟨e.trans permThreeEquivPSL⟩

end CFSG.Quasithin.F112R.St84
