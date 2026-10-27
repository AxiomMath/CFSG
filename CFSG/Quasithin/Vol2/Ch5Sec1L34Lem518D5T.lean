module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem518DLO
public import CFSG.Quasithin.Background.F918H3
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs518D5

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

section QuotO2

variable {G : Type} [Group G]

theorem map_conj_preimageModTwoCore {K : Subgroup G} (R : Subgroup (O2Q K))
    (g : ↥(Subgroup.normalizer (K : Set G))) :
    (preimageModTwoCore K R).map (MulAut.conj (g : G)).toMonoidHom =
      preimageModTwoCore K (R.map (quotConjAut K g).toMonoidHom) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyK, hyR⟩ := mem_preimageModTwoCore.mp hy
    exact mem_preimageModTwoCore.mpr ⟨(g.2 y).mp hyK, ⟨_, hyR, rfl⟩⟩
  · intro hx
    obtain ⟨hxK, r, hr, hrx⟩ := mem_preimageModTwoCore.mp hx
    have hyK : (g : G)⁻¹ * x * (g : G)⁻¹⁻¹ ∈ K := ((g⁻¹).2 x).mp hxK
    refine ⟨(g : G)⁻¹ * x * (g : G)⁻¹⁻¹, mem_preimageModTwoCore.mpr ⟨hyK, ?_⟩, ?_⟩
    · have e1 : quotConjAut K g⁻¹ (QuotientGroup.mk ⟨x, hxK⟩) =
          QuotientGroup.mk (⟨(g : G)⁻¹ * x * (g : G)⁻¹⁻¹, hyK⟩ : ↥K) :=
        quotConjAut_mk K g⁻¹ ⟨x, hxK⟩
      have e2 : quotConjAut K g⁻¹ (quotConjAut K g r) = r := by
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
      rw [← e1]
      have hrx' : quotConjAut K g r = QuotientGroup.mk ⟨x, hxK⟩ := hrx
      rw [← hrx', e2]
      exact hr
    · simp [MulAut.conj_apply, mul_assoc]

theorem imgO2_inf_normalizer_preimage {K : Subgroup G} (R : Subgroup (O2Q K)) :
    imgO2 K (K ⊓ Subgroup.normalizer (preimageModTwoCore K R : Set G)) =
      Subgroup.normalizer (R : Set (O2Q K)) := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    have h := mk_mem_normalizer_imgO2 (preimageModTwoCore_le K R) y.2 hy.2
    rw [imgO2_preimageModTwoCore] at h
    exact h
  · intro q hq
    induction q using QuotientGroup.induction_on with
    | H k =>
      have hkN : (k : G) ∈ Subgroup.normalizer (preimageModTwoCore K R : Set G) := by
        refine mem_normalizer_preimageModTwoCore
          (⟨(k : G), Subgroup.le_normalizer k.2⟩ : ↥(Subgroup.normalizer (K : Set G))) ?_
        rw [quotConjAut_of_mem k]
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hq
      exact mk_mem_imgO2 k.2 ⟨k.2, hkN⟩

variable [Finite G]

theorem oTwoUpper_subgroupOf_eq {K Y : Subgroup G} (hYK : Y ≤ K) :
    (oTwoUpper Y).subgroupOf K = oTwoUpper (Y.subgroupOf K) := by
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le ((oTwoUpper_le Y).trans hYK), ← oTwoUpper_map,
    Subgroup.map_subgroupOf_eq_of_le hYK]

theorem imgO2_oTwoUpper {K Y : Subgroup G} (hYK : Y ≤ K) :
    imgO2 K (oTwoUpper Y) = oTwoUpper (imgO2 K Y) := by
  rw [imgO2, imgO2, oTwoUpper_subgroupOf_eq hYK, oTwoUpper_map]

theorem le_of_imgO2_eq_top {X K J : Subgroup G} (hK : K = oTwoUpper X)
    (htop : imgO2 K J = ⊤) (hOJ : pCoreOf 2 K ≤ Subgroup.normalizer (J : Set G)) : K ≤ J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ∀ k ∈ K, Odd (orderOf k) → k ∈ J := by
    intro k hk hko
    have hmem : (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : O2Q K) ∈ imgO2 K J := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨j, hj, hjk⟩ := hmem
    replace hj : (j : G) ∈ J := hj
    have hq : ((j⁻¹ * ⟨k, hk⟩ : ↥K) : G) ∈ pCoreOf 2 K := by
      refine (mem_pCoreOf_iff_mk_eq_one (j⁻¹ * ⟨k, hk⟩).2).mpr ?_
      have hjk' : (QuotientGroup.mk j : O2Q K) = QuotientGroup.mk ⟨k, hk⟩ := hjk
      show (QuotientGroup.mk (j⁻¹ * ⟨k, hk⟩) : O2Q K) = 1
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hjk', inv_mul_cancel]
    set q : G := ((j⁻¹ * ⟨k, hk⟩ : ↥K) : G) with hqdef
    have hkjq : k = (j : G) * q := by simp [hqdef]
    obtain ⟨a, ha⟩ := (pCoreOf_isPGroup 2 K) ⟨q, hq⟩
    have hqa : q ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    obtain ⟨j', hj', hjq⟩ := A4.exists_pow_mul_eq hj (hOJ hq) (2 ^ a)
    have hk2 : k ^ 2 ^ a ∈ J := by
      rw [hkjq, hjq, hqa, mul_one]
      exact hj'
    have hcop : Nat.Coprime (2 ^ a) (orderOf k) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hko)
    have hz := A4.mem_zpowers_pow_of_coprime hcop
    exact (Subgroup.zpowers_le.mpr hk2) hz
  rw [hK]
  refine (Subgroup.closure_le J).mpr ?_
  rintro x ⟨hx, hxo⟩
  exact hodd x (hK ▸ mem_oTwoUpper_of_odd hx hxo) hxo

end QuotO2

section Setting

variable {G : Type} [Group G]

@[expose] def d518 (H D : Subgroup G) : Subgroup G :=
  D ⊓ Subgroup.normalizer (oTwoUpper H : Set G)

@[expose] def s518 (T H B D : Subgroup G) : Subgroup G :=
  pCoreOf 2 (d518 H D ⊔ B ⊔ T)

@[expose] def ParData518 (T H B D U : Subgroup G) : Prop :=
  pCoreOf 2 (oTwoUpper H) ≤ U ∧ U ≤ T ⊓ oTwoUpper H ∧
    d518 H D ⊔ B ⊔ s518 T H B D ≤ Subgroup.normalizer (U : Set G) ∧
    ∃ φ : ↥(oTwoUpper H ⊓ Subgroup.normalizer (U : Set G)) →*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2),
      Function.Surjective φ ∧
        φ.ker = U.subgroupOf (oTwoUpper H ⊓ Subgroup.normalizer (U : Set G))

structure Setting518D5 (G : Type) [Group G] [Finite G] (T M L V H B D D₃ D₅ : Subgroup G)
    (n : ℕ) : Prop where
  hyp : Hyp5_1_14 G T M L V H B D n
  D₃_le : D₃ ≤ D
  card_D₃ : Nat.card D₃ = 3
  D₃_le_Mp : D₃ ≤ Subgroup.normalizer (oTwoUpper H : Set G)
  outer : ∃ d ∈ D₃, ∀ k ∈ oTwoUpper H, d * k⁻¹ ∉ centralizerModO2 (oTwoUpper H)
  D₅_le : D₅ ≤ D
  card_D₅ : Nat.card D₅ = 5
  D₅_not_le : ¬ D₅ ≤ Subgroup.normalizer (oTwoUpper H : Set G)

theorem d518_le (H D : Subgroup G) : d518 H D ≤ D := inf_le_left

theorem d518_le_Mp (H D : Subgroup G) :
    d518 H D ≤ Subgroup.normalizer (oTwoUpper H : Set G) := inf_le_right

namespace Setting518D5

variable [Finite G] {T M L V H B D D₃ D₅ : Subgroup G} {n : ℕ}
  (s : Setting518D5 G T M L V H B D D₃ D₅ n)
include s

theorem exists_outer : ∃ d₀ ∈ d518 H D, d₀ ^ 3 = 1 ∧
    ∀ k ∈ oTwoUpper H, d₀ * k⁻¹ ∉ centralizerModO2 (oTwoUpper H) := by
  obtain ⟨d, hd, hdout⟩ := s.outer
  refine ⟨d, ⟨s.D₃_le hd, s.D₃_le_Mp hd⟩, ?_, hdout⟩
  have h' := pow_card_eq_one' (G := ↥D₃) (x := ⟨d, hd⟩)
  rw [s.card_D₃] at h'
  exact congrArg Subtype.val h'

theorem S_facts (h510 : Stmt5_1_10) (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) :
    s518 T H B D ≤ T ∧ T ⊓ L ≤ s518 T H B D ∧ T ⊓ oTwoUpper H ≤ s518 T H B D ∧
      pCoreOf 2 M ≤ s518 T H B D ∧
      pCoreOf 2 (Subgroup.normalizer (oTwoUpper H : Set G)) ≤ s518 T H B D ∧
      d518 H D ⊔ B ⊔ T ≤ Subgroup.normalizer (s518 T H B D : Set G) :=
  s.hyp.S_facts_of_le h510 h331 hR (d518_le H D) (d518_le_Mp H D)

theorem exists_two_parabolics (hTP : L34TwoParabolicFact) (hTA : L34TwoAutFact)
    (h510 : Stmt5_1_10) (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) :
    ∃ U₂ U₃ : Subgroup G, U₂ ≠ U₃ ∧ (∀ U : Subgroup G, (U = U₂ ∨ U = U₃) → ParData518 T H B D U) ∧
      oTwoUpper H ≤ oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U₂ : Set G)) ⊔
        oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U₃ : Set G)) ∧
      ∀ g ∈ Subgroup.normalizer (oTwoUpper H : Set G),
        g ∈ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) →
          (U₂.map (MulAut.conj g).toMonoidHom = U₂ ∨ U₂.map (MulAut.conj g).toMonoidHom = U₃) ∧
          (U₃.map (MulAut.conj g).toMonoidHom = U₂ ∨ U₃.map (MulAut.conj g).toMonoidHom = U₃) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := s.hyp
  set K := oTwoUpper H with hKdef
  set S := s518 T H B D with hSdef
  obtain ⟨hST, -, hTKS, -, -, hSN⟩ := s.S_facts h510 h331 hR
  obtain ⟨d₀, hd₀D, hd₀3, hd₀⟩ := s.exists_outer
  have hTK := h.isSylowTwoOf_inf_K
  have hOTK : pCoreOf 2 K ≤ T ⊓ K := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hTK
  have hBX : B ≤ d518 H D ⊔ B ⊔ T := le_sup_right.trans le_sup_left
  have hDX : d518 H D ≤ d518 H D ⊔ B ⊔ T := le_sup_left.trans le_sup_left
  have hXN := h.DBT_le_normalizer_inf_K_of_le h510 (d518_le H D) (d518_le_Mp H D)
  have hTMp := h.T_le_Mp
  obtain ⟨R₂, R₃, hne, hRfacts, hsup, hall⟩ :=
    hTP (O2Q K) h.l34 _ (isSylowTwoOf_imgO2 hTK)
  have hoddD : ∀ x ∈ d518 H D, Odd (orderOf x) := fun x hx =>
    h.notation59.2.1.2.1.of_dvd_nat
      (by rw [← Subgroup.orderOf_mk x ((d518_le H D) hx)]; exact orderOf_dvd_natCard _)
  have hoddB : ∀ x ∈ B, Odd (orderOf x) := fun x hx =>
    h.notation59.1.2.1.of_dvd_nat (by rw [← Subgroup.orderOf_mk x hx]; exact orderOf_dvd_natCard _)
  have hBK : B ≤ Subgroup.normalizer (K : Set G) :=
    h.notation59.1.1.trans (inf_le_right.trans (le_normalizer_oTwoUpper H))
  have hpar : ∀ R : Subgroup (O2Q K), (R = R₂ ∨ R = R₃) →
      ParData518 T H B D (preimageModTwoCore K R) := by
    intro R hRR
    obtain ⟨hRS, hNSR, -, -, ⟨π, hπs, hπk⟩, -, hodd⟩ := hRfacts R hRR
    set U := preimageModTwoCore K R with hUdef
    have hUK : U ≤ K := preimageModTwoCore_le K R
    have hOU : pCoreOf 2 K ≤ U := pCoreOf_le_preimageModTwoCore K R
    have hUTK : U ≤ T ⊓ K :=
      (preimageModTwoCore_mono hRS).trans (preimageModTwoCore_imgO2 hOTK inf_le_right).le
    have hRU : imgO2 K U = R := imgO2_preimageModTwoCore K R
    have hoddN : ∀ g ∈ Subgroup.normalizer (K : Set G),
        g ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) → Odd (orderOf g) →
          g ∈ Subgroup.normalizer (U : Set G) := by
      intro g hgK hgT hgo
      apply mem_normalizer_preimageModTwoCore ⟨g, hgK⟩
      apply hodd
      · refine hgo.of_dvd_nat ((orderOf_map_dvd _ _).trans ?_)
        rw [Subgroup.orderOf_mk]
      · exact map_quotConjAut_imgO2 inf_le_right ⟨g, hgK⟩ hgT
    refine ⟨hOU, hUTK, ?_, ?_⟩
    · refine sup_le (sup_le ?_ ?_) ?_
      · intro x hx
        exact hoddN x ((d518_le_Mp H D) hx) (hXN (hDX hx)) (hoddD x hx)
      · intro x hx
        exact hoddN x (hBK hx) (hXN (hBX hx)) (hoddB x hx)
      · intro x hx
        have hxN : x ∈ Subgroup.normalizer (K : Set G) := hTMp (hST hx)
        obtain ⟨y, hy, hye⟩ := h.quotConjAut_eq_conj_of_mem_S_of_le hTA h510 h331 hR (d518_le H D)
          (d518_le_Mp H D) hd₀D hd₀3 hd₀ hx hxN
        apply mem_normalizer_preimageModTwoCore ⟨x, hxN⟩
        rw [hye]
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNSR (Subgroup.le_normalizer hy))
    ·
      have hP : ∀ x : ↥(K ⊓ Subgroup.normalizer (U : Set G)),
          ((QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp (Subgroup.inclusion inf_le_left) x) ∈
            Subgroup.normalizer (R : Set (O2Q K)) := by
        intro x
        rw [← hRU]
        exact mk_mem_normalizer_imgO2 hUK x.2.1 x.2.2
      let ψ : ↥(K ⊓ Subgroup.normalizer (U : Set G)) →* ↥(Subgroup.normalizer (R : Set (O2Q K))) :=
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp (Subgroup.inclusion inf_le_left)).codRestrict
          _ hP
      refine ⟨π.comp ψ, ?_, ?_⟩
      · intro q
        obtain ⟨⟨y, hyP⟩, rfl⟩ := hπs q
        induction y using QuotientGroup.induction_on with
        | H k =>
          have hkN : (k : G) ∈ Subgroup.normalizer (U : Set G) := by
            refine mem_normalizer_preimageModTwoCore (K := K)
              (⟨(k : G), Subgroup.le_normalizer k.2⟩ : ↥(Subgroup.normalizer (K : Set G))) ?_
            rw [quotConjAut_of_mem k]
            exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hyP
          exact ⟨⟨k, k.2, hkN⟩, congrArg π (Subtype.ext rfl)⟩
      · ext x
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hπk,
          Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        constructor
        · intro hx
          exact mem_preimageModTwoCore.mpr ⟨x.2.1, hx⟩
        · intro hx
          exact (mem_preimageModTwoCore.mp hx).2
  refine ⟨preimageModTwoCore K R₂, preimageModTwoCore K R₃, ?_,
    fun U hU => ?_, ?_, ?_⟩
  · intro heq
    apply hne
    rw [← imgO2_preimageModTwoCore K R₂, heq, imgO2_preimageModTwoCore]
  · rcases hU with rfl | rfl
    · exact hpar R₂ (Or.inl rfl)
    · exact hpar R₃ (Or.inr rfl)
  ·
    set J := oTwoUpper (K ⊓ Subgroup.normalizer (preimageModTwoCore K R₂ : Set G)) ⊔
      oTwoUpper (K ⊓ Subgroup.normalizer (preimageModTwoCore K R₃ : Set G)) with hJ
    have himg : ∀ R : Subgroup (O2Q K), (R = R₂ ∨ R = R₃) →
        imgO2 K (oTwoUpper (K ⊓ Subgroup.normalizer (preimageModTwoCore K R : Set G))) =
          Subgroup.normalizer (R : Set (O2Q K)) := by
      intro R hRR
      rw [imgO2_oTwoUpper inf_le_left, imgO2_inf_normalizer_preimage]
      exact (hRfacts R hRR).2.2.2.2.2.1
    have htop : imgO2 K J = ⊤ := by
      rw [eq_top_iff, ← hsup, ← himg R₂ (Or.inl rfl), ← himg R₃ (Or.inr rfl)]
      exact sup_le (Subgroup.map_mono fun x hx =>
          Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx)))
        (Subgroup.map_mono fun x hx =>
          Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx)))
    have hOJ : pCoreOf 2 K ≤ Subgroup.normalizer (J : Set G) := by
      intro x hx
      have hxi : ∀ R : Subgroup (O2Q K), x ∈ Subgroup.normalizer
          (oTwoUpper (K ⊓ Subgroup.normalizer (preimageModTwoCore K R : Set G)) : Set G) := by
        intro R
        refine le_normalizer_oTwoUpper _ ⟨pCoreOf_le 2 K hx, ?_⟩
        exact Subgroup.le_normalizer (pCoreOf_le_preimageModTwoCore K R hx)
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, hJ, Subgroup.map_sup,
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hxi R₂),
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hxi R₃)]
    exact le_of_imgO2_eq_top rfl htop hOJ
  ·
    intro g hgK hgT
    have hα := map_quotConjAut_imgO2 inf_le_right ⟨g, hgK⟩ hgT
    obtain ⟨h2, h3⟩ := hall _ hα
    have e : ∀ R : Subgroup (O2Q K), (preimageModTwoCore K R).map (MulAut.conj g).toMonoidHom =
        preimageModTwoCore K (R.map (quotConjAut K ⟨g, hgK⟩).toMonoidHom) :=
      fun R => map_conj_preimageModTwoCore R ⟨g, hgK⟩
    refine ⟨?_, ?_⟩
    · rw [e]
      rcases h2 with h2 | h2 <;> rw [h2]
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rw [e]
      rcases h3 with h3 | h3 <;> rw [h3]
      · exact Or.inl rfl
      · exact Or.inr rfl

theorem normalizer_le_Mp (h311 : Theorem311Stmt) (h5114 : Stmt5_1_14_first) {R : Subgroup G}
    (hR1 : R ≠ ⊥) (hRT : R ≤ T) (hTKR : T ⊓ oTwoUpper H ≤ R)
    (hTR : T ≤ Subgroup.normalizer (R : Set G)) :
    Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := s.hyp
  have hh := h.hyp.toHyp5_0_1
  have hR2 : IsPGroup 2 R := hh.sylow.1.to_le hRT
  have hO : pCoreOf 2 (Subgroup.normalizer (R : Set G)) ≠ ⊥ := by
    intro h0
    apply hR1
    have hle : R ≤ pCoreOf 2 (Subgroup.normalizer (R : Set G)) :=
      le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hR2
    rw [h0] at hle
    exact le_bot_iff.mp hle
  have hM₀ : InH T (Subgroup.normalizer (R : Set G)) := ⟨hTR, hO⟩
  have hu : ∃ N : Subgroup G, IsUniqueMaxOver H T N := by
    obtain ⟨S, hS⟩ := exists_sylow_coe_eq hh.sylow
    have hstar : IsHStar (S : Subgroup G) M H := hS ▸ h.hyp.hStar
    have hTM : (S : Subgroup G) ≤ M := hS ▸ hh.T_le
    exact ⟨H ⊓ M, hS ▸ hstar.isUniqueMaxOver S hTM⟩
  have hTS : IsSylowTwoOf T (oTwoUpper H ⊔ T) := hh.isSylowTwoOf le_sup_right
  have hRS : IsSylowTwoOf R (oTwoUpper H ⊔ R) :=
    isSylowTwoOf_sup_of_inf_le hRT h.T_le_Mp (by rw [inf_comm]; exact hTKR) hTS
  obtain ⟨R₀, hR₀1, hR₀R, hR₀N⟩ := h311 G T hh.simple hh.nonabelian hh.qtke hh.sylow _ H R
    hM₀ h.hyp.hStar.1 hu hR1 hRT hRS le_rfl
  have hloc : IsTwoLocal (Subgroup.normalizer (R₀ : Set G)) := ⟨R₀, hR₀1, hR2.to_le hR₀R, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hHM' : H ≤ M' := le_sup_right.trans (hR₀N.trans hle)
  have hM'eq := (h.isUniqueM h5114).2 M' ⟨hM', hHM'⟩
  rw [← hM'eq]
  exact le_sup_left.trans (hR₀N.trans hle)

end Setting518D5

end Setting

end CFSG.Quasithin.H13
