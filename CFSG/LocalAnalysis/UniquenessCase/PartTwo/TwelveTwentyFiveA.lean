module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22p

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace TwelveTwentyFive

theorem pCoreOf_eq {M L : Subgroup G} (hL : F12.IsComponentModO2 M L) :
    pCoreOf 2 L = pCoreOf 2 M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPL, hLM, hsn, -⟩ := hL
  exact le_antisymm (A4.pCoreOf_le_of_subnormal 2 hsn)
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPL
      (hLM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M))

theorem exists_mem_commutator {M L : Subgroup G} (hL : F12.IsComponentModO2 M L) {x : G}
    (hx : x ∈ L) : ∃ y ∈ ⁅L, L⁆, y⁻¹ * x ∈ pCoreOf 2 M := by
  obtain ⟨-, -, -, hN, hq⟩ := id hL
  haveI := hN
  haveI : Group.IsPerfect (↥L ⧸ (pCoreOf 2 M).subgroupOf L) := hq.1
  set π := QuotientGroup.mk' ((pCoreOf 2 M).subgroupOf L) with hπ
  have h1 : π ⟨x, hx⟩ ∈ commutator (↥L ⧸ (pCoreOf 2 M).subgroupOf L) :=
    Group.IsPerfect.mem_commutator
  rw [commutator_def, ← Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _),
    ← Subgroup.map_commutator] at h1
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 h1
  refine ⟨y, ?_, ?_⟩
  · rw [← Subgroup.map_subtype_commutator]
    exact Subgroup.mem_map_of_mem _ hy
  · rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
    exact hyx

theorem isComponent_map {M L : Subgroup G} (hL : F12.IsComponentModO2 M L) :
    CFSG.IsComponent ((L.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLM, hsn, hN, hq⟩ := id hL
  haveI := hN
  set π : ↥M →* UC22.Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ∀ m : ↥M, π m = 1 ↔ (m : G) ∈ pCoreOf 2 M := by
    intro m
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (Subgroup.mem_map_iff_mem M.subtype_injective).symm
  set C := (L.subgroupOf M).map π with hC
  have hCsn : CFSG.Open.IsSubnormal C ⊤ := by
    have h1 := (hsn.comap M.subtype).map π
    have e1 : M.comap M.subtype = ⊤ := Subgroup.subgroupOf_self M
    rw [e1, Subgroup.map_top_of_surjective π hπs] at h1
    exact h1
  let φ : ↥L →* ↥C := (π.comp (Subgroup.inclusion hLM)).codRestrict C
    (fun l => ⟨Subgroup.inclusion hLM l, l.2, rfl⟩)
  have hφ : Function.Surjective φ := by
    rintro ⟨c, hc⟩
    obtain ⟨m, hm, rfl⟩ := hc
    exact ⟨⟨m, hm⟩, rfl⟩
  have hφker : ∀ l : ↥L, φ l = 1 ↔ l ∈ (pCoreOf 2 M).subgroupOf L := by
    intro l
    rw [Subgroup.mem_subgroupOf]
    refine Iff.trans ?_ (hker (Subgroup.inclusion hLM l))
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hkerφ : (pCoreOf 2 M).subgroupOf L ≤ φ.ker := fun l hl =>
    (MonoidHom.mem_ker).2 ((hφker l).2 hl)
  let ψ := QuotientGroup.lift ((pCoreOf 2 M).subgroupOf L) φ hkerφ
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hCne : Nontrivial ↥C := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    obtain ⟨a, b, hab⟩ := hq.2.2
    apply hab
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        have ha : a = 1 := by
          induction a using QuotientGroup.induction_on with
          | H l =>
            rw [QuotientGroup.eq_one_iff]
            exact (hφker l).1 (Subsingleton.elim _ _)
        have hb : b = 1 := by
          induction b using QuotientGroup.induction_on with
          | H l =>
            rw [QuotientGroup.eq_one_iff]
            exact (hφker l).1 (Subsingleton.elim _ _)
        rw [ha, hb]
  have hCq : CFSG.Open.IsQuasisimple ↥C :=
    uc22br4_isQuasisimple_of_surjective (A3.isQuasisimple_iff_open.mp hq) ψ hψ
  exact A3.isComponentOf_top_iff.1 ⟨le_top, hCsn, hCq⟩

theorem commutator_mem_pCoreOf {M L K A : Subgroup G} (hL : F12.IsComponentModO2 M L)
    (hKM : K ≤ M) (hKn : M ≤ normalizer (K : Set G)) (hPK : pCoreOf 2 M ≤ K) (hLK : ¬ L ≤ K)
    (hAM : A ≤ M) (hLA : ∀ x ∈ L, ∀ a ∈ A, ⁅x, a⁆ ∈ K) :
    ∀ x ∈ L, ∀ a ∈ A, ⁅x, a⁆ ∈ pCoreOf 2 M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : ↥M →* UC22.Bar2 M := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ∀ m : ↥M, π m = 1 ↔ (m : G) ∈ pCoreOf 2 M := by
    intro m
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (Subgroup.mem_map_iff_mem M.subtype_injective).symm
  have hLM : L ≤ M := hL.2.1
  have hC := isComponent_map hL
  set C := (L.subgroupOf M).map π with hCdef
  have hKs : ((K.subgroupOf M).map π).Normal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hKM).2 hKn).map π hπs
  have hCK : ¬ C ≤ (K.subgroupOf M).map π := by
    intro hle
    apply hLK
    intro y hy
    obtain ⟨k, hk, hkπ⟩ := hle ⟨⟨y, hLM hy⟩, hy, rfl⟩
    have h1 : π (k⁻¹ * ⟨y, hLM hy⟩) = 1 := by rw [map_mul, map_inv, hkπ, inv_mul_cancel]
    rw [hker] at h1
    have h4 : y = (k : G) * ((k⁻¹ * ⟨y, hLM hy⟩ : ↥M) : G) := by simp
    rw [h4]
    exact K.mul_mem hk (hPK h1)
  have hCKs : ⁅C, (K.subgroupOf M).map π⁆ = ⊥ :=
    (CFSG.LocalCores.component_normal_subgroup hC hKs).resolve_left hCK
  have hCA : ⁅C, (A.subgroupOf M).map π⁆ ≤ (K.subgroupOf M).map π := by
    rw [Subgroup.commutator_le]
    rintro _ ⟨y, hy, rfl⟩ _ ⟨a, ha, rfl⟩
    rw [← map_commutatorElement]
    exact ⟨⁅y, a⁆, hLA _ hy _ ha, rfl⟩
  have h2 : ⁅⁅C, (A.subgroupOf M).map π⁆, C⁆ = ⊥ := by
    refine le_bot_iff.1 ((Subgroup.commutator_mono hCA le_rfl).trans ?_)
    rw [Subgroup.commutator_comm, hCKs]
  have h3 := CFSG.LocalCores.perfect_double_commutator hC.1.1 h2
  intro y hy a ha
  have hmem : ⁅π ⟨y, hLM hy⟩, π ⟨a, hAM ha⟩⁆ ∈ ⁅C, (A.subgroupOf M).map π⁆ :=
    Subgroup.commutator_mem_commutator ⟨⟨y, hLM hy⟩, hy, rfl⟩ ⟨⟨a, hAM ha⟩, ha, rfl⟩
  rw [h3, Subgroup.mem_bot, ← map_commutatorElement, hker] at hmem
  exact hmem

theorem le_centralizer_of_forall_odd {M L V : Subgroup G} (hL : F12.IsComponentModO2 M L)
    (hMV : M ≤ normalizer (V : Set G)) (hPV : pCoreOf 2 M ≤ centralizer (V : Set G))
    (hodd : ∀ c ∈ L, Odd (orderOf c) → c ∈ centralizer (V : Set G)) :
    L ≤ centralizer (V : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLM, -, hN, hq⟩ := id hL
  haveI := hN
  haveI : Group.IsPerfect (↥L ⧸ (pCoreOf 2 M).subgroupOf L) := hq.1
  have hLN : L ≤ normalizer ((centralizer (V : Set G) : Subgroup G) : Set G) :=
    A1a.le_normalizer_centralizer (hLM.trans hMV)
  set N : Subgroup ↥L := (centralizer (V : Set G)).subgroupOf L with hNdef
  haveI hNn : N.Normal := ⟨fun n hn g => (Subgroup.mem_normalizer_iff.1 (hLN g.2) n).1 hn⟩
  have hker' : (pCoreOf 2 M).subgroupOf L ≤ (QuotientGroup.mk' N).ker := by
    intro x hx
    rw [QuotientGroup.ker_mk']
    exact hPV hx
  haveI : Group.IsPerfect (↥L ⧸ N) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.lift ((pCoreOf 2 M).subgroupOf L) (QuotientGroup.mk' N) hker')
    (by
      intro q
      induction q using QuotientGroup.induction_on with
      | H x => exact ⟨QuotientGroup.mk x, rfl⟩)
  have h2 : IsPGroup 2 (↥L ⧸ N) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      have hpos : orderOf (x : G) ≠ 0 := (orderOf_pos (x : G)).ne'
      obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hpos
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      show ((x ^ 2 ^ k : ↥L) : G) ∈ centralizer (V : Set G)
      rw [Subgroup.coe_pow]
      refine hodd _ (L.pow_mem x.2 _) ?_
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, hkm⟩, hkm,
        Nat.mul_div_cancel_left _ (pow_pos two_pos k)]
      exact hm
  have hsub : Subsingleton (↥L ⧸ N) := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isNilpotent (↥L ⧸ N) h2.isNilpotent
  intro x hx
  have h1 : (QuotientGroup.mk (⟨x, hx⟩ : ↥L) : ↥L ⧸ N) = 1 := Subsingleton.elim _ _
  rw [QuotientGroup.eq_one_iff] at h1
  exact h1

theorem mem_centralizer_of_odd (D : Data G) {V : Subgroup G} (hV : InCalV D.M V) {c : G}
    (hcM : c ∈ D.M) (hc : Odd (orderOf c))
    (hcJ : ∀ j ∈ F12.jOf D.T, ⁅c, j⁆ ∈ centralizer (V : Set G))
    (hcE : c ∈ centralizer (proofE D : Set G)) : c ∈ centralizer (V : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMV : D.M ≤ normalizer (V : Set G) := hV.2.2.1
  have hV2 : IsPGroup 2 ↥V := uc22p22e_isPGroup_of_elem hV.2.2.2
  let φ := uc22br4_conjAut D.M V hMV
  let B : Subgroup ↥D.M := (F12.jOf D.T).subgroupOf D.M
  have hB : IsPGroup 2 ↥B :=
    ((D.sylowM.isPGroup).to_le (uc22p22e_jOf_le_self D.T)).comap_subtype
  let cM : ↥D.M := ⟨c, hcM⟩
  have hord : Odd (orderOf cM) := by rw [← Subgroup.orderOf_coe]; exact hc
  have hcB : ∀ b ∈ B, φ cM * φ b = φ b * φ cM := by
    intro b hb
    have hd := hcJ (b : G) hb
    ext v
    show c * ((b : G) * v * (b : G)⁻¹) * c⁻¹ = (b : G) * (c * v * c⁻¹) * (b : G)⁻¹
    have hw : (b : G) * (c * (v : G) * c⁻¹) * (b : G)⁻¹ ∈ V :=
      uc22br_gt_conj_mem hMV b.2 (uc22br_gt_conj_mem hMV hcM v.2)
    have hcen := Subgroup.mem_centralizer_iff.1 hd _ hw
    calc c * ((b : G) * v * (b : G)⁻¹) * c⁻¹
        = ⁅c, (b : G)⁆ * ((b : G) * (c * v * c⁻¹) * (b : G)⁻¹) * ⁅c, (b : G)⁆⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = (b : G) * (c * v * c⁻¹) * (b : G)⁻¹ := by
          rw [← hcen]; group
  have hfix : ∀ r : ↥V, (∀ b ∈ B, φ b r = r) → φ cM r = r := by
    intro r hr
    have hrT : (r : G) ∈ D.T := uc22p22p_le_T_of_inCalV D hV r.2
    have hrc : ∀ j ∈ F12.jOf D.T, j * (r : G) = (r : G) * j := by
      intro j hj
      have h1 := congrArg Subtype.val
        (hr ⟨j, D.sylowM.le (uc22p22e_jOf_le_self D.T hj)⟩ hj)
      have h2 : j * (r : G) * j⁻¹ = r := h1
      calc j * (r : G) = j * (r : G) * j⁻¹ * j := by group
        _ = (r : G) * j := by rw [h2]
    have hrE : (r : G) ∈ proofE D :=
      uc22p22e_mem_omegaZJ'.2 ⟨hrT, hrc, hV.2.2.2.2 (r : G) r.2⟩
    have h3 := Subgroup.mem_centralizer_iff.1 hcE (r : G) hrE
    apply Subtype.ext
    show c * (r : G) * c⁻¹ = r
    calc c * (r : G) * c⁻¹ = (r : G) * c * c⁻¹ := by rw [← h3]
      _ = r := by group
  have h1 := uc22p22e_thompson φ hV2 hB hord hcB hfix
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h2 : c * v * c⁻¹ = v :=
    congrArg (fun f : MulAut ↥V => ((f ⟨v, hv⟩ : ↥V) : G)) h1
  calc v * c = c * v * c⁻¹ * c := by rw [h2]
    _ = c * v := by group

theorem conj_mem_jOf (D : Data G) {L : Subgroup G} (hL : F12.IsComponentModO2 D.M L)
    (hJL : ⁅F12.jOf D.T, L⁆ ≤ pCoreOf 2 L) {y : G} (hy : y ∈ L) :
    ∀ x ∈ F12.jOf D.T, y * x * y⁻¹ ∈ F12.jOf D.T := by
  refine uc22p22e_conj_jOf (fun x hx => ?_)
  have h1 : ⁅x, y⁆ ∈ pCoreOf 2 L := hJL (Subgroup.commutator_mem_commutator hx hy)
  rw [pCoreOf_eq hL] at h1
  have h2 : ⁅y, x⁆ ∈ D.T := by
    rw [← commutatorElement_inv]
    exact D.T.inv_mem (uc22p22e_pCoreOf_le_T D h1)
  have h3 : y * x * y⁻¹ = ⁅y, x⁆ * x := by simp only [commutatorElement_def]; group
  rw [h3]
  exact D.T.mul_mem h2 (uc22p22e_jOf_le_self D.T hx)

theorem le_normalizer_proofE (D : Data G) {L : Subgroup G} (hL : F12.IsComponentModO2 D.M L)
    (hJL : ⁅F12.jOf D.T, L⁆ ≤ pCoreOf 2 L) : L ≤ normalizer (proofE D : Set G) := by
  intro y hy
  have h1 := conj_mem_jOf D hL hJL hy
  have h2 : ∀ x ∈ F12.jOf D.T, y⁻¹ * x * y ∈ F12.jOf D.T := fun x hx => by
    simpa using conj_mem_jOf D hL hJL (L.inv_mem hy) x hx
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact fun hz => uc22p22e_conj_omegaZJ h1 h2 z hz
  · intro hz
    have := uc22p22e_conj_omegaZJ (y := y⁻¹) (by simpa using h2) (by simpa using h1) _ hz
    show z ∈ omegaZJ22 D.T
    simpa [mul_assoc] using this

theorem T_le_normalizer_proofE (D : Data G) : D.T ≤ normalizer (proofE D : Set G) := by
  intro y hy
  have h1 := uc22p22e_normalizes_jOf_T D y hy
  have h2 : ∀ x ∈ F12.jOf D.T, y⁻¹ * x * y ∈ F12.jOf D.T := fun x hx => by
    simpa using uc22p22e_normalizes_jOf_T D y⁻¹ (D.T.inv_mem hy) x hx
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact fun hz => uc22p22e_conj_omegaZJ h1 h2 z hz
  · intro hz
    have := uc22p22e_conj_omegaZJ (y := y⁻¹) (by simpa using h2) (by simpa using h1) _ hz
    show z ∈ omegaZJ22 D.T
    simpa [mul_assoc] using this

end TwelveTwentyFive

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
