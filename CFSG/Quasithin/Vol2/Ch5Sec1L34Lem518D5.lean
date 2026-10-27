module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem518D5S
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Lie
public import CFSG.Quasithin.Vol2.Ch12Sec8OneL1
public import CFSG.Quasithin.EmptyFaithful.F918C1
public import CFSG.Quasithin.Background.A3Structure314
public import CFSG.Quasithin.H13.A7Nat1238QTabList
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped commutatorElement Pointwise

section General

variable {G : Type} [Group G]

theorem map_conj_eq_iff_of_perm {U U' : Subgroup G} (hne : U ≠ U') {g : G}
    (hg : (U.map (MulAut.conj g).toMonoidHom = U ∨ U.map (MulAut.conj g).toMonoidHom = U') ∧
      (U'.map (MulAut.conj g).toMonoidHom = U ∨ U'.map (MulAut.conj g).toMonoidHom = U')) :
    U.map (MulAut.conj g).toMonoidHom = U ↔ U'.map (MulAut.conj g).toMonoidHom = U' := by
  have hinj := Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  obtain ⟨h1, h2⟩ := hg
  constructor
  · intro hU
    rcases h2 with h2 | h2
    · exact absurd (hinj (h2.trans hU.symm)).symm hne
    · exact h2
  · intro hU'
    rcases h1 with h1 | h1
    · exact h1
    · exact absurd (hinj (h1.trans hU'.symm)) hne

theorem map_conj_inf_normalizer {K U : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    (K ⊓ Subgroup.normalizer (U : Set G)).map (MulAut.conj g).toMonoidHom =
      K ⊓ Subgroup.normalizer ((U.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  have hK : K.map (MulAut.conj g).toMonoidHom = K := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, hK]
  congr 1
  exact Subgroup.map_equiv_normalizer_eq U (MulAut.conj g)

variable [Finite G] in
theorem eq_oTwoUpper_sup_of_isSylowTwoOf {X T : Subgroup G} (hT : IsSylowTwoOf T X) :
    X = oTwoUpper X ⊔ T :=
  le_antisymm (F7.isSylowTwoOf_le_sup_of_two_power hT (le_normalizer_oTwoUpper X)
    (fun _ hx => exists_pow_mem_oTwoUpper X hx)) (sup_le (oTwoUpper_le X) hT.1)

end General

section Swap

variable {G : Type} [Group G]

theorem map_conj_mul (U : Subgroup G) (x y : G) :
    U.map (MulAut.conj (x * y)).toMonoidHom =
      (U.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.map_map, map_mul]
  rfl

theorem mem_normalizer_map_conj_inv {U : Subgroup G} {a y : G}
    (hy : a * y * a⁻¹ ∈ Subgroup.normalizer (U : Set G)) :
    y ∈ Subgroup.normalizer ((U.map (MulAut.conj a⁻¹).toMonoidHom : Subgroup G) : Set G) := by
  rw [← Subgroup.map_equiv_normalizer_eq]
  refine ⟨a * y * a⁻¹, hy, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  group

theorem le_normalizer_inf_normalizer_of_swap {T U U' : Subgroup G}
    (hfix : ∀ t ∈ T, (t ∈ Subgroup.normalizer (U : Set G) ↔
      t ∈ Subgroup.normalizer (U' : Set G)))
    (hswap : ∀ t ∈ T, t ∉ Subgroup.normalizer (U : Set G) →
      U.map (MulAut.conj t).toMonoidHom = U') :
    T ≤ Subgroup.normalizer ((T ⊓ Subgroup.normalizer (U : Set G) : Subgroup G) : Set G) := by
  intro t ht
  have hiff : ∀ y ∈ T, (y ∈ Subgroup.normalizer (U : Set G) ↔
      t * y * t⁻¹ ∈ Subgroup.normalizer (U : Set G)) := by
    intro y hy
    have hty : t * y * t⁻¹ ∈ T := T.mul_mem (T.mul_mem ht hy) (T.inv_mem ht)
    by_cases htU : t ∈ Subgroup.normalizer (U : Set G)
    · constructor
      · intro hyU
        exact (Subgroup.normalizer (U : Set G)).mul_mem
          ((Subgroup.normalizer (U : Set G)).mul_mem htU hyU)
          ((Subgroup.normalizer (U : Set G)).inv_mem htU)
      · intro hyU
        have := (Subgroup.normalizer (U : Set G)).mul_mem
          ((Subgroup.normalizer (U : Set G)).mul_mem
            ((Subgroup.normalizer (U : Set G)).inv_mem htU) hyU) htU
        simpa [mul_assoc] using this
    · have hUt := hswap t ht htU
      have key : y ∈ Subgroup.normalizer (U : Set G) ↔
          t * y * t⁻¹ ∈ Subgroup.normalizer (U' : Set G) := by
        rw [← hUt, ← Subgroup.map_equiv_normalizer_eq]
        constructor
        · intro hyU
          exact ⟨y, hyU, by simp [MulAut.conj_apply]⟩
        · rintro ⟨z, hz, hzy⟩
          have : z = y := by
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzy
            exact mul_left_cancel (mul_right_cancel hzy)
          rwa [← this]
      rw [key, ← hfix _ hty]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxT, hxU⟩
    exact ⟨T.mul_mem (T.mul_mem ht hxT) (T.inv_mem ht), (hiff x hxT).mp hxU⟩
  · rintro ⟨hxT, hxU⟩
    have hxT' : x ∈ T := by
      have := T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht
      simpa [mul_assoc] using this
    exact ⟨hxT', (hiff x hxT').mpr hxU⟩

theorem card_eq_two_mul_of_swap [Finite G] {T U U' : Subgroup G}
    (hswap : ∀ t ∈ T, t ∉ Subgroup.normalizer (U : Set G) →
      U.map (MulAut.conj t).toMonoidHom = U')
    (hswap' : ∀ t ∈ T, t ∉ Subgroup.normalizer (U : Set G) →
      U'.map (MulAut.conj t).toMonoidHom = U)
    {t : G} (htT : t ∈ T) (htU : t ∉ Subgroup.normalizer (U : Set G)) :
    Nat.card T = 2 * Nat.card (T ⊓ Subgroup.normalizer (U : Set G) : Subgroup G) := by
  have hUt := hswap t htT htU
  have hidx2 : ((T ⊓ Subgroup.normalizer (U : Set G)).subgroupOf T).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨t, htT⟩, fun b => ?_⟩
    rw [xor_iff_iff_not, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have hbT : (b : G) ∈ T := b.2
    show (b : G) * t ∈ T ⊓ Subgroup.normalizer (U : Set G) ↔
      ¬ (b : G) ∈ T ⊓ Subgroup.normalizer (U : Set G)
    constructor
    · rintro ⟨-, hbtU⟩ ⟨-, hbU⟩
      apply htU
      have := (Subgroup.normalizer (U : Set G)).mul_mem
        ((Subgroup.normalizer (U : Set G)).inv_mem hbU) hbtU
      simpa using this
    · intro hbT₀
      have hbU : (b : G) ∉ Subgroup.normalizer (U : Set G) := fun h' => hbT₀ ⟨hbT, h'⟩
      refine ⟨T.mul_mem hbT htT, ?_⟩
      show (b : G) * t ∈ Subgroup.normalizer (U : Set G)
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      show U.map (MulAut.conj ((b : G) * t)).toMonoidHom = U
      rw [map_conj_mul, hUt, hswap' _ hbT hbU]
  have h1 := ((T ⊓ Subgroup.normalizer (U : Set G)).subgroupOf T).card_mul_index
  rw [hidx2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h1
  omega

theorem card_le_of_quasithinIsSylowTwo [Finite G] {T P : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hP : IsPGroup 2 P) : Nat.card P ≤ Nat.card T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨S₀, hS₀⟩ := exists_sylow_coe_eq hT
  calc Nat.card P ≤ Nat.card Q := Subgroup.card_le_of_le hQ
    _ = Nat.card S₀ := by rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    _ = Nat.card T := by rw [← hS₀]

theorem relIndex_eq_two_of_lt [Finite G] {T₀ T₁ : Subgroup G} (hlt : T₀ < T₁)
    (hT₁ : IsPGroup 2 T₁) (hcard : Nat.card T₁ ≤ 2 * Nat.card T₀) :
    T₀.relIndex T₁ = 2 ∧ Nat.card T₁ = 2 * Nat.card T₀ := by
  have hrel := Subgroup.relIndex_mul_card T₀ T₁
  rw [inf_eq_left.mpr hlt.le] at hrel
  have hrel1 : T₀.relIndex T₁ ≠ 1 := fun h1 =>
    hlt.ne' (le_antisymm (Subgroup.relIndex_eq_one.mp h1) hlt.le)
  have hrel2 : 2 ≤ T₀.relIndex T₁ := by
    obtain ⟨k, hk⟩ := hT₁.exists_card_eq
    have hdvd : T₀.relIndex T₁ ∣ 2 ^ k := hk ▸ Subgroup.relIndex_dvd_card T₀ T₁
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rcases j with _ | j
    · exact absurd (by simpa using hj) hrel1
    · rw [hj, pow_succ]
      have := Nat.one_le_two_pow (n := j)
      omega
  have hpos : 0 < Nat.card T₀ := Nat.card_pos
  have h3 : T₀.relIndex T₁ * Nat.card T₀ ≤ 2 * Nat.card T₀ := by rw [hrel]; exact hcard
  have h4 := Nat.le_of_mul_le_mul_right h3 hpos
  have h5 : T₀.relIndex T₁ = 2 := by omega
  refine ⟨h5, ?_⟩
  rw [← hrel, h5]

theorem isSylowTwoOf_of_card_eq [Finite G] {T T₁ A : Subgroup G} (hTA : IsSylowTwoOf T A)
    (hT₁A : T₁ ≤ A) (hT₁ : IsPGroup 2 T₁) (hcard : Nat.card T₁ = Nat.card T) :
    IsSylowTwoOf T₁ A := by
  refine ⟨hT₁A, hT₁, ?_⟩
  have e1 := Subgroup.relIndex_mul_card T₁ A
  have e2 := Subgroup.relIndex_mul_card T A
  rw [inf_eq_left.mpr hT₁A, hcard] at e1
  rw [inf_eq_left.mpr hTA.1] at e2
  have hpos : 0 < Nat.card T := Nat.card_pos
  have heq : T₁.relIndex A = T.relIndex A := Nat.eq_of_mul_eq_mul_right hpos (e1.trans e2.symm)
  show ¬ 2 ∣ T₁.relIndex A
  rw [heq]
  exact hTA.2.2

end Swap

section Bar

variable {G : Type} [Group G] [Finite G]

theorem isPerfect_of_isSimpleGroup {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hp : ¬ (Nat.card Q).Prime) : Group.IsPerfect Q := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
  · exfalso
    have hc : ∀ a b : Q, a * b = b * a := by
      intro a b
      have h1 : ⁅a, b⁆ ∈ commutator Q :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_def] at h1
      exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
    let _ : CommGroup Q := { (inferInstance : Group Q) with mul_comm := hc }
    exact hp IsSimpleGroup.prime_card
  · exact ⟨h⟩

theorem isQuasisimple_of_nonempty_psl24 {Q : Type*} [Group Q]
    (h : Nonempty (Q ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2))) :
    CFSG.IsQuasisimple Q := by
  obtain ⟨e⟩ := h
  have := isSimpleGroup_psl24
  have hs : IsSimpleGroup Q := e.isSimpleGroup
  have : Finite Q := Finite.of_equiv _ e.symm.toEquiv
  have hcard : Nat.card Q = 60 := by rw [Nat.card_congr e.toEquiv, card_psl24']
  have hp : ¬ (Nat.card Q).Prime := by rw [hcard]; norm_num
  exact isQuasisimple_of_perfect_of_isSimpleGroup (isPerfect_of_isSimpleGroup hp) hs

omit [Finite G] in
theorem modO2Image_inf_eq {X P K : Subgroup G} (hOP : pCoreOf 2 X ≤ P) :
    modO2Image X (P ⊓ K) = modO2Image X P ⊓ modO2Image X K := by
  apply le_antisymm
  · exact le_inf (Subgroup.map_mono fun x hx => (Subgroup.mem_subgroupOf.mp hx).1)
      (Subgroup.map_mono fun x hx => (Subgroup.mem_subgroupOf.mp hx).2)
  · rintro _ ⟨⟨p, hp, hpk⟩, ⟨k, hk, rfl⟩⟩
    replace hp : (p : G) ∈ P := Subgroup.mem_subgroupOf.mp hp
    replace hk : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
    have hpk' : p⁻¹ * k ∈ CFSG.pCore 2 ↥X := by
      rw [← QuotientGroup.eq]
      exact hpk
    have hO : ((p⁻¹ * k : ↥X) : G) ∈ pCoreOf 2 X := by
      exact ⟨_, hpk', rfl⟩
    have hkP : (k : G) ∈ P := by
      have := P.mul_mem hp (hOP hO)
      simpa using this
    exact ⟨k, Subgroup.mem_subgroupOf.mpr ⟨hkP, hk⟩, rfl⟩

omit [Finite G] in
theorem modO2Image_set_mul_comm {X A C : Subgroup G} (hAX : A ≤ X) (hCX : C ≤ X)
    (h₁ : ∀ a ∈ A, ∀ c ∈ C, ∃ a' ∈ A, ∃ c' ∈ C, c * a = a' * c')
    (h₂ : ∀ a ∈ A, ∀ c ∈ C, ∃ c' ∈ C, ∃ a' ∈ A, a * c = c' * a') :
    (modO2Image X A : Set (O2Q X)) * (modO2Image X C : Set (O2Q X)) =
      (modO2Image X C : Set (O2Q X)) * (modO2Image X A : Set (O2Q X)) := by
  ext x
  simp only [Set.mem_mul, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨c, hc, rfl⟩, rfl⟩
    obtain ⟨c', hc', a', ha', he⟩ :=
      h₂ a (Subgroup.mem_subgroupOf.mp ha) c (Subgroup.mem_subgroupOf.mp hc)
    refine ⟨_, ⟨⟨c', hCX hc'⟩, Subgroup.mem_subgroupOf.mpr hc', rfl⟩, _,
      ⟨⟨a', hAX ha'⟩, Subgroup.mem_subgroupOf.mpr ha', rfl⟩, ?_⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext he.symm)
  · rintro ⟨_, ⟨c, hc, rfl⟩, _, ⟨a, ha, rfl⟩, rfl⟩
    obtain ⟨a', ha', c', hc', he⟩ :=
      h₁ a (Subgroup.mem_subgroupOf.mp ha) c (Subgroup.mem_subgroupOf.mp hc)
    refine ⟨_, ⟨⟨a', hAX ha'⟩, Subgroup.mem_subgroupOf.mpr ha', rfl⟩, _,
      ⟨⟨c', hCX hc'⟩, Subgroup.mem_subgroupOf.mpr hc', rfl⟩, ?_⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext he.symm)

theorem mem_normalizer_of_mk_mem_normalizer {X K : Subgroup G} (hKX : K ≤ X) (hK : ⁅K, K⁆ = K)
    (hOK : pCoreOf 2 X ≤ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ X)
    (hxK : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨x, hx⟩ ∈
      Subgroup.normalizer ((modO2Image X K : Subgroup (O2Q X)) : Set (O2Q X))) :
    x ∈ Subgroup.normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmK : ∀ y ∈ K, x * y * x⁻¹ ∈ K ⊔ pCoreOf 2 X := by
    intro y hy
    have hyX : y ∈ X := hKX hy
    obtain ⟨z, hz, hzy⟩ := (Subgroup.mem_normalizer_iff.mp hxK
      (QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨y, hyX⟩)).mp ⟨⟨y, hyX⟩, hy, rfl⟩
    have h2 : z⁻¹ * (⟨x, hx⟩ * ⟨y, hyX⟩ * ⟨x, hx⟩⁻¹) ∈ CFSG.pCore 2 ↥X := by
      have h' : QuotientGroup.mk' (CFSG.pCore 2 ↥X) z =
          QuotientGroup.mk' (CFSG.pCore 2 ↥X) (⟨x, hx⟩ * ⟨y, hyX⟩ * ⟨x, hx⟩⁻¹) := by
        rw [hzy, map_mul, map_mul, map_inv]
      rwa [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h'
    have h2' : z⁻¹ * (⟨x, hx⟩ * ⟨y, hyX⟩ * ⟨x, hx⟩⁻¹) ∈ CFSG.Open.pCore 2 ↥X := by
      exact h2
    have h3 : x * y * x⁻¹ = (z : G) *
        ((z⁻¹ * (⟨x, hx⟩ * ⟨y, hyX⟩ * ⟨x, hx⟩⁻¹) : ↥X) : G) := by
      simp
    rw [h3]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hz))
      (Subgroup.mem_sup_right ⟨_, h2', rfl⟩)
  have hle : K.map (MulAut.conj x).toMonoidHom ≤ K := by
    refine le_of_perfect_of_le_sup (by rw [← Subgroup.map_commutator, hK]) ?_
      (pCoreOf_isPGroup 2 X) hOK
    rintro _ ⟨y, hy, rfl⟩
    exact hmK y hy
  have hcard : Nat.card (K.map (MulAut.conj x).toMonoidHom) = Nat.card K :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge hle hcard.ge)

theorem a314Statement_bar (hQ : quasithinIsQTKECat G)
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (h36 : A36ForSQTK)
    (h312 : A312ForSQTK) (h314 : A314Facts) {X T₀ B L : Subgroup G}
    (hO : pCoreOf 2 X ≠ ⊥) (hsyl : IsSylowTwoOf T₀ X) (hBX : B ≤ X) (hB : B ∈ lFamily T₀)
    (hL : L ∈ cComp X) (hBL : B < L) (hT₀B : T₀ ≤ Subgroup.normalizer (B : Set G))
    (hA : Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* alternatingGroup (Fin 5))) :
    modO2Image X B < modO2Image X L ∧
      A314Statement (o2Img X T₀) (modO2Image X B) (modO2Image X L) := by
  have hne : modO2Image X B ≠ modO2Image X L := fun h =>
    hBL.ne (Vol2.Ch11.SecA.eq_of_modO2Image_eq hsyl (le_of_mem_cComp hL) hBL.le
      (perfect_of_mem_cComp hL) hT₀B h)
  have hlt : modO2Image X B < modO2Image X L :=
    lt_of_le_of_ne (Subgroup.map_mono fun _ hx => hBL.le hx) hne
  refine ⟨hlt, ?_⟩
  have hQbar := sqtkHyp_quotient_of_pCoreOf_ne_bot hQ hs hnab hO
  have hsylbar : IsSylowTwoOf (o2Img X T₀) ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hsyl) _
      (QuotientGroup.mk'_surjective _)
  have hL' : modO2Image X L ∈ cComp (⊤ : Subgroup (O2Q X)) := modO2Image_mem_cComp hL
  have hBbar : modO2Image X B ∈ lFamily (o2Img X T₀) := modO2Image_mem_lFamily hsyl hBX hB
  have hTL : IsSylowTwoOf (o2Img X T₀ ⊓ modO2Image X L) (modO2Image X L) :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hL') hsylbar
  have hB1 : modO2Image X B ∈ lFamily (o2Img X T₀ ⊓ modO2Image X L) :=
    cComp_mem_of_le hBbar le_sup_left (sup_le_sup_left inf_le_left _)
  have hAbar : IsAlt 5 (↥(modO2Image X B) ⧸ CFSG.solvableRadical ↥(modO2Image X B)) :=
    A7.isAlt_quot_solvableRadical_of_surj hA (barMap_surjective hBX) (isPGroup_ker_barMap _)
  rcases lemma_1_2_4_list hQ hs hnab h312 hO hsyl hBX hB hL hBL.le with h1 | h1 | h1
  · exact absurd h1 hne
  · exact A314.of_case h314 ⟨hBbar, hlt, hTL, hB1, hAbar⟩ h1
  · rcases A314.nonquasi_case (h36 _ hQbar _ hL') (A312.not_quasisimple_of_nonquasi h1) hlt
      hAbar h1 with h13 | h14
    · unfold A314Statement
      iterate 12 right
      left
      exact h13
    · unfold A314Statement
      iterate 13 right
      exact h14

theorem le_centralizer_of_card_three_of_card_five {B E : Subgroup G} (hB : Nat.card B = 3)
    (hE : Nat.card E = 5) (hBE : B ≤ Subgroup.normalizer (E : Set G)) :
    B ≤ Subgroup.centralizer (E : Set G) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : IsCyclic ↥E := isCyclic_of_prime_card (p := 5) hE
  let ρ : ↥B →* MulAut ↥E := E.normalizerMonoidHom.comp (Subgroup.inclusion hBE)
  have hAut : Nat.card (MulAut ↥E) = 4 := by
    rw [IsCyclic.card_mulAut, hE]
    decide
  have h3 : Nat.card ρ.range ∣ 3 := hB ▸ Subgroup.card_range_dvd ρ
  have h4 : Nat.card ρ.range ∣ 4 := hAut ▸ Subgroup.card_subgroup_dvd_card ρ.range
  have h1 : Nat.card ρ.range = 1 := by
    have := Nat.dvd_gcd h3 h4
    simpa using this
  have hbot : ρ.range = ⊥ := (Subgroup.eq_bot_iff_card ρ.range).mpr h1
  intro b hb
  have hρb : ρ ⟨b, hb⟩ = 1 := by
    have : ρ ⟨b, hb⟩ ∈ ρ.range := ⟨⟨b, hb⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have hker : (⟨b, hBE hb⟩ : ↥(Subgroup.normalizer (E : Set G))) ∈ E.normalizerMonoidHom.ker :=
    hρb
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hker
  exact hker

end Bar

section Setting

variable {G : Type} [Group G]

namespace Setting518D5

variable [Finite G] {T M L V H B D D₃ D₅ : Subgroup G} {n : ℕ}
  (s : Setting518D5 G T M L V H B D D₃ D₅ n)
include s

theorem T_le_normalizer_inf_K :
    T ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := fun _ ht =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, s.hyp.T_le_Mp ht⟩

theorem le_Mp_of_conj (h5114 : Stmt5_1_14_first) {Y : Subgroup G} {a : G}
    (haMp : a ∈ Subgroup.normalizer (oTwoUpper H : Set G)) (hKY : oTwoUpper H ≤ Y)
    (hTY : ∀ y ∈ T, a * y * a⁻¹ ∈ Y) (hO : pCoreOf 2 Y ≠ ⊥) :
    Y ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := s.hyp
  have hh := h.hyp.toHyp5_0_1
  have hYQ : Y ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) := le_normalizer_pCoreOf 2 Y
  have hHQ' : H ≤ Subgroup.normalizer
      (((pCoreOf 2 Y).map (MulAut.conj a⁻¹).toMonoidHom : Subgroup G) : Set G) := by
    rw [eq_oTwoUpper_sup_of_isSylowTwoOf (hh.isSylowTwoOf h.hyp.hStar.1.1)]
    refine sup_le (fun k hk => mem_normalizer_map_conj_inv (hYQ (hKY ?_)))
      (fun y hy => mem_normalizer_map_conj_inv (hYQ (hTY y hy)))
    exact (Subgroup.mem_normalizer_iff.mp haMp k).mp hk
  have hQ'1 : (pCoreOf 2 Y).map (MulAut.conj a⁻¹).toMonoidHom ≠ ⊥ := fun h0 =>
    hO ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj a⁻¹).injective).mp h0)
  have hloc : IsTwoLocal (Subgroup.normalizer
      (((pCoreOf 2 Y).map (MulAut.conj a⁻¹).toMonoidHom : Subgroup G) : Set G)) :=
    ⟨_, hQ'1, (pCoreOf_isPGroup 2 Y).map _, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hM'eq := (h.isUniqueM h5114).2 M' ⟨hM', hHQ'.trans hle⟩
  intro y hy
  have h1 : a⁻¹ * y * a⁻¹⁻¹ ∈ Subgroup.normalizer
      (((pCoreOf 2 Y).map (MulAut.conj a⁻¹).toMonoidHom : Subgroup G) : Set G) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact ⟨y, hYQ hy, rfl⟩
  have h2 : a⁻¹ * y * a⁻¹⁻¹ ∈ Subgroup.normalizer (oTwoUpper H : Set G) := by
    rw [← hM'eq]
    exact hle h1
  have h3 := (Subgroup.normalizer (oTwoUpper H : Set G)).mul_mem
    ((Subgroup.normalizer (oTwoUpper H : Set G)).mul_mem haMp h2)
    ((Subgroup.normalizer (oTwoUpper H : Set G)).inv_mem haMp)
  simpa [mul_assoc] using h3

omit s in
theorem K_le_of_swap {U U' Y : Subgroup G} {t₁ : G}
    (ht₁Mp : t₁ ∈ Subgroup.normalizer (oTwoUpper H : Set G)) (ht₁Y : t₁ ∈ Y)
    (hUt₁ : U.map (MulAut.conj t₁).toMonoidHom = U')
    (hK : oTwoUpper H ≤ oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔
      oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U' : Set G)))
    (hK₂Y : oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ≤ Y) :
    oTwoUpper H ≤ Y := by
  have hK₃eq : (oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G))).map
      (MulAut.conj t₁).toMonoidHom =
        oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U' : Set G)) := by
    rw [← oTwoUpper_map, map_conj_inf_normalizer ht₁Mp, hUt₁]
  refine hK.trans (sup_le hK₂Y ?_)
  rw [← hK₃eq]
  rintro _ ⟨k, hk, rfl⟩
  exact Y.mul_mem (Y.mul_mem ht₁Y (hK₂Y hk)) (Y.inv_mem ht₁Y)

theorem isSylowTwoOf_T₀ (hF : L2TorusFact) (h311 : Theorem311Stmt) (h5114 : Stmt5_1_14_first)
    (h510 : Stmt5_1_10) (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) {U U' : Subgroup G}
    (hUU' : U ≠ U') (hU : ParData518 T H B D U)
    (hK : oTwoUpper H ≤ oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔
      oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U' : Set G)))
    (hperm : ∀ g ∈ Subgroup.normalizer (oTwoUpper H : Set G),
      g ∈ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) →
        (U.map (MulAut.conj g).toMonoidHom = U ∨ U.map (MulAut.conj g).toMonoidHom = U') ∧
        (U'.map (MulAut.conj g).toMonoidHom = U ∨ U'.map (MulAut.conj g).toMonoidHom = U'))
    (hO : pCoreOf 2 (oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔
      sd5 T L H B D D₅) ≠ ⊥) :
    IsSylowTwoOf (T ⊓ Subgroup.normalizer (U : Set G))
      ((oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔ sd5 T L H B D D₅) ⊔
        (T ⊓ Subgroup.normalizer (U : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := s.hyp
  have hh := h.hyp.toHyp5_0_1
  obtain ⟨hST, -, hTKS, hOMS, -, hSN⟩ := s.S_facts h510 h331 hR
  obtain ⟨-, -, hUN, -⟩ := hU
  have hTMp := h.T_le_Mp
  have hTTK := s.T_le_normalizer_inf_K
  have hfix : ∀ g ∈ Subgroup.normalizer (oTwoUpper H : Set G),
      g ∈ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) →
        (g ∈ Subgroup.normalizer (U : Set G) ↔ g ∈ Subgroup.normalizer (U' : Set G)) := by
    intro g hgK hgT
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.mem_normalizer_iff_map_conj_eq]
    exact map_conj_eq_iff_of_perm hUU' (hperm g hgK hgT)
  have hswap : ∀ g ∈ Subgroup.normalizer (oTwoUpper H : Set G),
      g ∈ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) →
        g ∉ Subgroup.normalizer (U : Set G) → U.map (MulAut.conj g).toMonoidHom = U' := by
    intro g hgK hgT hgU
    rcases (hperm g hgK hgT).1 with h1 | h1
    · exact absurd (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1) hgU
    · exact h1
  have hswap' : ∀ g ∈ Subgroup.normalizer (oTwoUpper H : Set G),
      g ∈ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) →
        g ∉ Subgroup.normalizer (U : Set G) → U'.map (MulAut.conj g).toMonoidHom = U := by
    intro g hgK hgT hgU
    rcases (hperm g hgK hgT).2 with h1 | h1
    · exact h1
    · exact absurd ((hfix g hgK hgT).mpr (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1)) hgU
  have hST₀ : s518 T H B D ≤ T ⊓ Subgroup.normalizer (U : Set G) :=
    le_inf hST (le_sup_right.trans hUN)
  have hTKT₀ : T ⊓ oTwoUpper H ≤ T ⊓ Subgroup.normalizer (U : Set G) := hTKS.trans hST₀
  have hT₀2 : IsPGroup 2 ↥(T ⊓ Subgroup.normalizer (U : Set G) : Subgroup G) :=
    hh.sylow.1.to_le inf_le_left
  have hTT₀ := le_normalizer_inf_normalizer_of_swap (U := U) (U' := U')
    (fun t ht => hfix t (hTMp ht) (hTTK ht)) (fun t ht => hswap t (hTMp ht) (hTTK ht))
  have hT₀1 : T ⊓ Subgroup.normalizer (U : Set G) ≠ ⊥ := by
    intro h0
    apply pCoreOf_ne_bot_of_isTwoLocal hh.maxTwoLocal.1
    have hle := hOMS.trans hST₀
    rw [h0] at hle
    exact le_bot_iff.mp hle
  have hNT₀ := s.normalizer_le_Mp h311 h5114 hT₀1 inf_le_left hTKT₀ hTT₀
  have hT₀X : T ⊓ Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer
      ((oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔ sd5 T L H B D D₅ :
        Subgroup G) : Set G) :=
    le_normalizer_sup_of_le
      (fun x hx => Hyp5_1_14.mem_normalizer_oTwoUpper_inf (hTMp hx.1) hx.2)
      (inf_le_left.trans (le_normalizer_sup_of_le (s.T_le_normalizer_z518 hF)
        (le_sup_right.trans hSN)))
  have hOX : pCoreOf 2 (oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔
      sd5 T L H B D D₅) ≤ pCoreOf 2 ((oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔
        sd5 T L H B D D₅) ⊔ (T ⊓ Subgroup.normalizer (U : Set G))) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left)
      ((sup_le Subgroup.le_normalizer hT₀X).trans (normalizer_le_normalizer_pCoreOf 2 _))
      (pCoreOf_isPGroup 2 _)
  set X₁ := (oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔ sd5 T L H B D D₅) ⊔
    (T ⊓ Subgroup.normalizer (U : Set G)) with hX₁def
  clear_value X₁
  have hT₀X₁ : T ⊓ Subgroup.normalizer (U : Set G) ≤ X₁ := by rw [hX₁def]; exact le_sup_right
  have hK₂X₁ : oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ≤ X₁ := by
    rw [hX₁def]; exact le_sup_left.trans le_sup_left
  have hD₅X₁ : D₅ ≤ X₁ := by
    rw [hX₁def]
    exact (le_sup_right.trans le_sup_left : D₅ ≤ sd5 T L H B D D₅).trans
      (le_sup_right.trans le_sup_left)
  have hOX₁ : pCoreOf 2 X₁ ≠ ⊥ := by
    intro h0
    apply hO
    rw [h0] at hOX
    exact le_bot_iff.mp hOX
  by_contra hns
  obtain ⟨T₁, hT₁, hT₀T₁⟩ := A4.exists_isSylowTwoOf_ge hT₀X₁ hT₀2
  have hlt : T ⊓ Subgroup.normalizer (U : Set G) < T₁ := by
    refine lt_of_le_of_ne hT₀T₁ (fun heq => hns ?_)
    rw [← heq] at hT₁
    exact hT₁
  obtain ⟨t, htT, htU⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (U : Set G) := by
    by_contra hall
    push Not at hall
    have hTeq : T ⊓ Subgroup.normalizer (U : Set G) = T :=
      le_antisymm inf_le_left (fun x hx => ⟨hx, hall x hx⟩)
    apply hns
    have hTX₁ : T ≤ X₁ := by rw [← hTeq]; exact hT₀X₁
    rw [hTeq]
    exact hh.isSylowTwoOf hTX₁
  have hcT := card_eq_two_mul_of_swap (fun t ht => hswap t (hTMp ht) (hTTK ht))
    (fun t ht => hswap' t (hTMp ht) (hTTK ht)) htT htU
  have hcT₁le : Nat.card T₁ ≤ 2 * Nat.card (T ⊓ Subgroup.normalizer (U : Set G) : Subgroup G) := by
    rw [← hcT]
    exact card_le_of_quasithinIsSylowTwo hh.sylow hT₁.2.1
  obtain ⟨hrel2, hcT₁⟩ := relIndex_eq_two_of_lt hlt hT₁.2.1 hcT₁le
  have hT₁N : T₁ ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.normalizer (U : Set G) : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hT₀T₁).mp
      (Subgroup.normal_of_index_eq_two hrel2)
  have hT₁Mp := hT₁N.trans hNT₀
  have hT₀K : (T ⊓ Subgroup.normalizer (U : Set G)) ⊓ oTwoUpper H = T ⊓ oTwoUpper H :=
    le_antisymm (inf_le_inf_right _ inf_le_left) (le_inf hTKT₀ inf_le_right)
  have hT₁TK : T₁ ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
    rw [← hT₀K]
    exact fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨hT₁N hx, hT₁Mp hx⟩
  have hTA := hh.isSylowTwoOf (le_inf hTMp hTTK)
  have hT₁A := isSylowTwoOf_of_card_eq hTA (le_inf hT₁Mp hT₁TK) hT₁.2.1 (hcT₁.trans hcT.symm)
  obtain ⟨a, haA, ha⟩ := A4.exists_conj_of_isSylowTwoOf hTA hT₁A
  have hconjT : ∀ y ∈ T, a * y * a⁻¹ ∈ T₁ := fun y hy =>
    (ha _).mpr (by simpa [mul_assoc] using hy)
  have hnot : ¬ T₁ ≤ Subgroup.normalizer (U : Set G) := by
    intro hT₁U
    have hTUa : T ≤ Subgroup.normalizer
        ((U.map (MulAut.conj a⁻¹).toMonoidHom : Subgroup G) : Set G) := fun y hy =>
      mem_normalizer_map_conj_inv (hT₁U (hconjT y hy))
    rcases (hperm a⁻¹ (inv_mem haA.1) (inv_mem haA.2)).1 with h1 | h1
    · rw [h1] at hTUa
      exact htU (hTUa htT)
    · rw [h1] at hTUa
      exact htU ((hfix t (hTMp htT) (hTTK htT)).mpr (hTUa htT))
  obtain ⟨t₁, ht₁T₁, ht₁U⟩ := Set.not_subset.mp hnot
  have hKX₁ := K_le_of_swap (hT₁Mp ht₁T₁) (hT₁.1 ht₁T₁)
    (hswap t₁ (hT₁Mp ht₁T₁) (hT₁TK ht₁T₁) ht₁U) hK hK₂X₁
  have hX₁Mp := s.le_Mp_of_conj h5114 haA.1 hKX₁ (fun y hy => hT₁.1 (hconjT y hy)) hOX₁
  exact s.D₅_not_le (hD₅X₁.trans hX₁Mp)

theorem parabolic_facts (h510 : Stmt5_1_10) (h331 : Stmt3_3_1)
    (hR : L2RankOneSylowFact)
    {U : Subgroup G} (hU : ParData518 T H B D U) :
    T ⊓ Subgroup.normalizer (U : Set G) ≤
        Subgroup.normalizer (oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) : Set G) ∧
      oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ∈
        lFamily (T ⊓ Subgroup.normalizer (U : Set G)) ∧
      Nonempty (↥(oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G))) ⧸
        CFSG.pCore 2 ↥(oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G))) ≃*
          alternatingGroup (Fin 5)) ∧
      B ≤ oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ∧
      B ≤ Subgroup.normalizer (((T ⊓ Subgroup.normalizer (U : Set G)) ⊓
        oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := s.hyp
  set K₂ := oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) with hK₂def
  obtain ⟨hST, -, hTKS, -, -, -⟩ := s.S_facts h510 h331 hR
  obtain ⟨-, hUTK, hUN, φ, hφs, hφk⟩ := hU
  have hTK := h.isSylowTwoOf_inf_K
  have hTKN : T ⊓ oTwoUpper H ≤ Subgroup.normalizer (U : Set G) :=
    hTKS.trans (le_sup_right.trans hUN)
  obtain ⟨hL2K₂, -, -, -, -⟩ := oTwoUpper_parabolic_facts rfl hTK hUTK hTKN φ hφs hφk
  have hTMp := h.T_le_Mp
  have hT₀K₂ : T ⊓ Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (K₂ : Set G) :=
    fun x hx => Hyp5_1_14.mem_normalizer_oTwoUpper_inf (hTMp hx.1) hx.2
  obtain ⟨e⟩ := hL2K₂
  have e' : ↥K₂ ⧸ CFSG.pCore 2 ↥K₂ ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2)
      (GaloisField 2 2) := (QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K₂ 2)).trans e
  have := isSimpleGroup_psl24
  obtain ⟨eA⟩ := CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five
    (G := Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) card_psl24'
  have hq : CFSG.IsQuasisimple (↥K₂ ⧸ CFSG.pCore 2 ↥K₂) := isQuasisimple_of_nonempty_psl24 ⟨e'⟩
  have hsub : IsSubnormal K₂ (K₂ ⊔ (T ⊓ Subgroup.normalizer (U : Set G))) :=
    A4.subnormal_of_normal le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hT₀K₂))
  have hlfam : K₂ ∈ lFamily (T ⊓ Subgroup.normalizer (U : Set G)) :=
    mem_cComp_of_quasisimple_quotient (oTwoUpper_eq_top_of_isPGroup _) hq hsub
  have hBK₂ : B ≤ K₂ := by
    intro b hb
    have hodd : Odd (orderOf b) := h.notation59.1.2.1.of_dvd_nat
      (by rw [← Subgroup.orderOf_mk b hb]; exact orderOf_dvd_natCard _)
    exact mem_oTwoUpper_of_odd ⟨h.mem_K_of_mem_B hb,
      hUN (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb))⟩ hodd
  have hBT : B ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) :=
    (le_sup_right.trans le_sup_left).trans
      (h.DBT_le_normalizer_inf_K_of_le h510 (d518_le H D) (d518_le_Mp H D))
  have hK₂K : K₂ ≤ oTwoUpper H := (oTwoUpper_le _).trans inf_le_left
  have heq : (T ⊓ Subgroup.normalizer (U : Set G)) ⊓ K₂ = (T ⊓ oTwoUpper H) ⊓ K₂ := by
    apply le_antisymm
    · exact le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans hK₂K)) inf_le_right
    · exact le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans hTKN))
        inf_le_right
  refine ⟨hT₀K₂, hlfam, ⟨e'.trans eA⟩, hBK₂, ?_⟩
  rw [heq]
  exact fun b hb => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hBT hb, Subgroup.le_normalizer (hBK₂ hb)⟩

theorem D₅_le_normalizer_of_sylow (hF : L2TorusFact)
    (h510 : Stmt5_1_10) (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK)
    (h314 : A314Facts) (hFive : A314FiveNormFact) {U X₁ : Subgroup G}
    (hU : ParData518 T H B D U)
    (hX₁ : X₁ = (oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔
      sd5 T L H B D D₅) ⊔ (T ⊓ Subgroup.normalizer (U : Set G)))
    (hsyl : IsSylowTwoOf (T ⊓ Subgroup.normalizer (U : Set G)) X₁) (hO : pCoreOf 2 X₁ ≠ ⊥) :
    D₅ ≤ Subgroup.normalizer
      (oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := s.hyp
  have hh := h.hyp.toHyp5_0_1
  obtain ⟨hT₀K₂, hlfam, hA5, hBK₂, hBT₀⟩ := s.parabolic_facts h510 h331 hR hU
  set K₂ := oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) with hK₂def
  set T₀ := T ⊓ Subgroup.normalizer (U : Set G) with hT₀def
  have hK₂X₁ : K₂ ≤ X₁ := by rw [hX₁]; exact le_sup_left.trans le_sup_left
  have hT₀X₁ : T₀ ≤ X₁ := hsyl.1
  have hD₅X₁ : D₅ ≤ X₁ := by
    rw [hX₁]
    exact (le_sup_right.trans le_sup_left : D₅ ≤ sd5 T L H B D D₅).trans
      (le_sup_right.trans le_sup_left)
  have hperf : ⁅K₂, K₂⁆ = K₂ := perfect_of_mem_cComp hlfam
  have hOT₀ : pCoreOf 2 X₁ ≤ T₀ := F7.isSylowTwoOf_pCoreOf_le hsyl
  obtain ⟨KX, hKX, hK₂KX⟩ := lemma_1_2_4_exists hh.qtke hh.simple hh.nonabelian h37 h39 hO hsyl
    hK₂X₁ hlfam
  have hnorm := lemma_1_2_4_normal hh.qtke hh.simple hh.nonabelian h37 h38 hO hsyl hlfam hK₂KX
    hKX hT₀K₂
  have hX₁KX : X₁ ≤ Subgroup.normalizer (KX : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hKX)).mp hnorm
  rcases eq_or_lt_of_le hK₂KX with heq | hlt
  · rw [heq]
    exact hD₅X₁.trans hX₁KX
  obtain ⟨hltbar, h314bar⟩ := a314Statement_bar hh.qtke hh.simple hh.nonabelian h36 h312 h314
    hO hsyl hK₂X₁ hlfam hKX hlt hT₀K₂ hA5
  have hQbar := sqtkHyp_quotient_of_pCoreOf_ne_bot hh.qtke hh.simple hh.nonabelian hO
  have hsylbar : IsSylowTwoOf (o2Img X₁ T₀) ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hsyl) _
      (QuotientGroup.mk'_surjective _)
  have hBbar := modO2Image_mem_lFamily hsyl hK₂X₁ hlfam
  have hA5bar : IsAlt 5 (ModO2 (modO2Image X₁ K₂)) := by
    obtain ⟨e1⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv hK₂X₁
    obtain ⟨e2⟩ := hA5
    exact ⟨e1.symm.trans e2⟩
  have hLbar := modO2Image_mem_cComp hKX
  have hD5card : Nat.card (modO2Image X₁ D₅) = 5 := by
    have hker : (barMap hD₅X₁).ker = ⊥ := by
      have h2 := isPGroup_ker_barMap hD₅X₁
      obtain ⟨k, hk⟩ := h2.exists_card_eq
      have hdvd : 2 ^ k ∣ 5 := hk ▸ s.card_D₅ ▸ Subgroup.card_subgroup_dvd_card _
      have hk0 : k = 0 := by
        rcases k with _ | k
        · rfl
        · exfalso
          rw [pow_succ] at hdvd
          have : 2 ∣ 5 := (dvd_mul_left 2 (2 ^ k)).trans hdvd
          omega
      rw [hk0, pow_zero] at hk
      exact Subgroup.eq_bot_of_card_eq _ hk
    have hinj : Function.Injective (barMap hD₅X₁) := (MonoidHom.ker_eq_bot_iff _).mp hker
    rw [← Nat.card_congr (Equiv.ofBijective _ ⟨hinj, barMap_surjective hD₅X₁⟩), s.card_D₅]
  have hD5N : modO2Image X₁ D₅ ≤
      Subgroup.normalizer ((modO2Image X₁ KX : Subgroup (O2Q X₁)) : Set (O2Q X₁)) := by
    rintro _ ⟨d, -, rfl⟩
    exact o2Map_mem_normalizer (hX₁KX d.2)
  have hT0N : o2Img X₁ T₀ ≤
      Subgroup.normalizer ((modO2Image X₁ KX : Subgroup (O2Q X₁)) : Set (O2Q X₁)) := by
    rintro _ ⟨t, -, rfl⟩
    exact o2Map_mem_normalizer (hX₁KX t.2)
  have hT0B : o2Img X₁ T₀ ≤
      Subgroup.normalizer ((modO2Image X₁ K₂ : Subgroup (O2Q X₁)) : Set (O2Q X₁)) := by
    rintro _ ⟨t, ht, rfl⟩
    exact o2Map_mem_normalizer (hT₀K₂ (Subgroup.mem_subgroupOf.mp ht))
  obtain ⟨hST, hTLS, -, -, -, -⟩ := s.S_facts h510 h331 hR
  have hTLT₀ : T ⊓ L ≤ T₀ := hTLS.trans (le_inf hST (le_sup_right.trans hU.2.2.1))
  have hZT := s.T_le_normalizer_z518 hF
  have hDN := s.D₅_le_normalizer_inf
  have hset1 : ((z518 T L D₅ : Subgroup G) : Set G) =
      (D₅ : Set G) * ((T ⊓ L : Subgroup G) : Set G) := by
    rw [z518, sup_comm]
    exact Subgroup.coe_mul_of_left_le_normalizer_right D₅ (T ⊓ L) hDN
  have hset2 : ((z518 T L D₅ : Subgroup G) : Set G) =
      ((T ⊓ L : Subgroup G) : Set G) * (D₅ : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left (T ⊓ L) D₅ hDN
  have h₁ : ∀ a ∈ D₅, ∀ c ∈ T₀, ∃ a' ∈ D₅, ∃ c' ∈ T₀, c * a = a' * c' := by
    intro a ha c hc
    have hca : c * a * c⁻¹ ∈ ((z518 T L D₅ : Subgroup G) : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (hZT hc.1) a).mp (Subgroup.mem_sup_right ha)
    rw [hset1] at hca
    obtain ⟨a', ha', l, hl, hal⟩ := hca
    have hal' : a' * l = c * a * c⁻¹ := hal
    refine ⟨a', ha', l * c, T₀.mul_mem (hTLT₀ hl) hc, ?_⟩
    calc c * a = (c * a * c⁻¹) * c := by group
      _ = (a' * l) * c := by rw [← hal']
      _ = a' * (l * c) := by group
  have h₂ : ∀ a ∈ D₅, ∀ c ∈ T₀, ∃ c' ∈ T₀, ∃ a' ∈ D₅, a * c = c' * a' := by
    intro a ha c hc
    have hca : c⁻¹ * a * c⁻¹⁻¹ ∈ ((z518 T L D₅ : Subgroup G) : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (hZT (T.inv_mem hc.1)) a).mp (Subgroup.mem_sup_right ha)
    rw [hset2] at hca
    obtain ⟨l, hl, a', ha', hla⟩ := hca
    have hla' : l * a' = c⁻¹ * a * c⁻¹⁻¹ := hla
    refine ⟨c * l, T₀.mul_mem hc (hTLT₀ hl), a', ha', ?_⟩
    calc a * c = c * (c⁻¹ * a * c⁻¹⁻¹) := by group
      _ = c * (l * a') := by rw [← hla']
      _ = c * l * a' := by group
  have hDT := modO2Image_set_mul_comm hD₅X₁ hT₀X₁ h₁ h₂
  have hB3 : Nat.card B = 3 := h.card_B_eq_three h510
  obtain ⟨⟨b, hbB⟩, hb3⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 3 (by rw [hB3])
  have hb3' : orderOf b = 3 := by rw [← Subgroup.orderOf_mk b hbB]; exact hb3
  have hbX₁ : b ∈ X₁ := hK₂X₁ (hBK₂ hbB)
  have hBD : B ≤ Subgroup.normalizer (D₅ : Set G) := fun x hx =>
    mem_normalizer_of_le_isCyclic (s.isCyclic_D hF) s.D₅_le (h.notation59.2.2 hx)
  have hBC := le_centralizer_of_card_three_of_card_five hB3 s.card_D₅ hBD
  have hb : ∃ y ∈ modO2Image X₁ K₂, orderOf y = 3 ∧
      y ∈ Subgroup.normalizer ((o2Img X₁ T₀ ⊓ modO2Image X₁ K₂ : Subgroup (O2Q X₁)) :
        Set (O2Q X₁)) ∧ ∀ d ∈ modO2Image X₁ D₅, d * y = y * d := by
    refine ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥X₁) ⟨b, hbX₁⟩, ⟨⟨b, hbX₁⟩, hBK₂ hbB, rfl⟩, ?_,
      ?_, ?_⟩
    · have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥X₁) ⟨b, hbX₁⟩) ^ 3 = 1 := by
        rw [← map_pow]
        have : (⟨b, hbX₁⟩ : ↥X₁) ^ 3 = 1 := Subtype.ext (by simp [← hb3', pow_orderOf_eq_one])
        rw [this, map_one]
      have hne : QuotientGroup.mk' (CFSG.pCore 2 ↥X₁) ⟨b, hbX₁⟩ ≠ 1 := by
        intro h0
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h0
        obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥X₁)) ⟨_, h0⟩
        have hbk : b ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val (congrArg Subtype.val hk)
        have := orderOf_dvd_of_pow_eq_one hbk
        rw [hb3'] at this
        have h3 := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three this)
        omega
      have hdvd := orderOf_dvd_of_pow_eq_one h1
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h' | h'
      · exact absurd (orderOf_eq_one_iff.mp h') hne
      · exact h'
    · show _ ∈ Subgroup.normalizer ((modO2Image X₁ T₀ ⊓ modO2Image X₁ K₂ :
        Subgroup (O2Q X₁)) : Set (O2Q X₁))
      rw [← modO2Image_inf_eq hOT₀]
      exact o2Map_mem_normalizer (hBT₀ hbB)
    · rintro _ ⟨d, hd, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have hc := hBC hbB
      exact (Subgroup.mem_centralizer_iff.mp hc d (Subgroup.mem_subgroupOf.mp hd))
  have hDK := hFive (O2Q X₁) hQbar (o2Img X₁ T₀) (modO2Image X₁ K₂) (modO2Image X₁ KX)
    (modO2Image X₁ D₅) hsylbar hBbar hA5bar hLbar hltbar h314bar hD5card hD5N hT0N hT0B hDT hb
  intro d hd
  exact mem_normalizer_of_mk_mem_normalizer hK₂X₁ hperf (hOT₀.trans hT₀K₂) (hD₅X₁ hd)
    (hDK ⟨⟨d, hD₅X₁ hd⟩, hd, rfl⟩)

theorem pCoreOf_X₁_ne_bot (hF : L2TorusFact) (h510 : Stmt5_1_10) (h331 : Stmt3_3_1)
    (hR : L2RankOneSylowFact) {U : Subgroup G}
    (hO : pCoreOf 2 (oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔
      sd5 T L H B D D₅) ≠ ⊥) :
    pCoreOf 2 ((oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔ sd5 T L H B D D₅) ⊔
      (T ⊓ Subgroup.normalizer (U : Set G))) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, hSN⟩ := s.S_facts h510 h331 hR
  have hTMp := s.hyp.T_le_Mp
  have hT₀X : T ⊓ Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer
      ((oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔ sd5 T L H B D D₅ :
        Subgroup G) : Set G) :=
    le_normalizer_sup_of_le
      (fun x hx => Hyp5_1_14.mem_normalizer_oTwoUpper_inf (hTMp hx.1) hx.2)
      (inf_le_left.trans (le_normalizer_sup_of_le (s.T_le_normalizer_z518 hF)
        (le_sup_right.trans hSN)))
  have hOX := le_pCoreOf_of_le_normalizer 2
    ((pCoreOf_le 2 (oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) ⊔
      sd5 T L H B D D₅)).trans (le_sup_left (b := T ⊓ Subgroup.normalizer (U : Set G))))
    ((sup_le Subgroup.le_normalizer hT₀X).trans (normalizer_le_normalizer_pCoreOf 2 _))
    (pCoreOf_isPGroup 2 _)
  intro h0
  rw [h0] at hOX
  exact hO (le_bot_iff.mp hOX)

end Setting518D5

end Setting

end CFSG.Quasithin.H13
