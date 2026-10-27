module

public import CFSG.Quasithin.H13.A6S4L0
public import CFSG.Quasithin.H13.U3L14D6
public import CFSG.Quasithin.Vol2.Ch3Sec2IrrPlus
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.H13.L32NNotation
public import CFSG.Quasithin.H13.U3L15Core

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem twoReduced_R2 (X : Subgroup G) : IsTwoReducedIn X (reducedAggregate X) := by
  have h := A4.isTwoReducedIn_twoReducedJoin X
  rwa [← primeReducedAggregate_map_subtype_eq_twoReducedJoin] at h

omit [Finite G] in
theorem le_R2_of_isTwoReducedIn {X W : Subgroup G} (h : IsTwoReducedIn X W) :
    W ≤ reducedAggregate X := by
  rw [show reducedAggregate X = twoReducedJoin X from
    primeReducedAggregate_map_subtype_eq_twoReducedJoin X]
  exact le_iSup₂_of_le (f := fun (V : Subgroup G) (_ : IsTwoReducedIn X V) => V) W h le_rfl

theorem pCoreOf_le_centralizer_R2 (X : Subgroup G) :
    pCoreOf 2 X ≤ centralizer (reducedAggregate X : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (twoReduced_R2 X).2.2.2 _ (pCoreOf_le 2 X) (le_normalizer_pCoreOf 2 X) fun d hd => ?_
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 X ⟨d, hd⟩
  refine ⟨k, ?_⟩
  have : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  rw [this]
  exact one_mem _

theorem R2_le_pCoreOf (X : Subgroup G) : reducedAggregate X ≤ pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hle, hN, hel, -⟩ := twoReduced_R2 X
  refine le_pCoreOf_of_le_normalizer 2 hle hN fun v => ⟨1, ?_⟩
  exact Subtype.ext (by simpa using hel.2 v v.2)

theorem R2_le_of_le {T X H : Subgroup G} (hT : IsSylowTwoOf T H) (hchar : CharTwo H)
    (hTX : T ≤ X) (hXH : X ≤ H) : reducedAggregate X ≤ reducedAggregate H := by
  rw [show reducedAggregate X = twoReducedJoin X from
      primeReducedAggregate_map_subtype_eq_twoReducedJoin X,
    show reducedAggregate H = twoReducedJoin H from
      primeReducedAggregate_map_subtype_eq_twoReducedJoin H]
  exact twoReducedProduct_le_of_isSylowIn hT hchar hTX hXH

omit [Finite G] in
theorem isIrrPlusIn_self_mono {X A A' W : Subgroup G} (hAA' : A ≤ A')
    (h : IsIrrPlusIn X A X W) : IsIrrPlusIn X A' X W := by
  obtain ⟨hWA, hW1, hXW, hcomm, hlt, hirr, -⟩ := h
  refine ⟨hWA.trans hAA', hW1, hXW, hcomm, hlt, hirr, fun J _ hJ _ _ => hJ.trans ?_⟩
  exact sup_le_sup_right
    (conjClosure_le fun x hx w hw => (mem_normalizer_iff.mp (hXW hx) w).mp hw) _

theorem inf_centralizer_ne_bot_of_two {P W : Subgroup G} (hP : IsPGroup 2 P) (hWP : W ≤ P)
    (hnorm : P ≤ normalizer (W : Set G)) (hW : W ≠ ⊥) : W ⊓ centralizer (P : Set G) ≠ ⊥ := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have hnormal : (W.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hnorm
  have hne : W.subgroupOf P ≠ ⊥ := by
    intro h
    apply hW
    rw [← map_subgroupOf_eq_of_le hWP, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ :=
    ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : G) ∈ centralizer (P : Set G) := by
    rw [mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h
  have hmem : (y : G) ∈ W ⊓ centralizer (P : Set G) := ⟨hy.1, hyC⟩
  rw [h, mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

omit [Finite G] in
theorem mem_normalizer_commutator {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [map_commutator, hA, hB]

omit [Finite G] in
theorem center_eq_bot_of_mulEquiv {Q A : Type*} [Group Q] [Group A] (e : Q ≃* A)
    (hA : center A = ⊥) : center Q = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have h1 : e z ∈ center A := by
    rw [mem_center_iff] at hz ⊢
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hz g']
  rw [hA, mem_bot, map_eq_one_iff e e.injective] at h1
  rw [h1]
  exact one_mem _

omit [Finite G] in
theorem center_eq_bot_of_surjective {A B : Type*} [Group A] [Group B] [IsSimpleGroup A]
    (hA : center A = ⊥) [Nontrivial B] (π : A →* B) (hπ : Function.Surjective π) :
    center B = ⊥ := by
  have hinj : Function.Injective π := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff π).1 h
    · exfalso
      obtain ⟨b, hb⟩ := exists_ne (1 : B)
      obtain ⟨a, rfl⟩ := hπ b
      exact hb ((MonoidHom.mem_ker).1 (h ▸ mem_top a))
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨a, rfl⟩ := hπ z
  have ha : a ∈ center A := by
    rw [mem_center_iff] at hz ⊢
    intro g
    apply hinj
    rw [map_mul, map_mul]
    exact hz (π g)
  rw [hA, mem_bot] at ha
  rw [ha, map_one]
  exact one_mem _

omit [Finite G] in
theorem center_eq_bot_of_alt {B : Type*} [Group B] [Nontrivial B] {n : ℕ} (hn : 5 ≤ n)
    (π : ↥(alternatingGroup (Fin n)) →* B) (hπ : Function.Surjective π) : center B = ⊥ := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  exact center_eq_bot_of_surjective
    (alternatingGroup.center_eq_bot (by simp [Nat.card_eq_fintype_card]; omega)) π hπ

omit [Finite G] in
theorem center_SL32_eq_bot : center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = ⊥ := by
  refine eq_bot_iff.2 fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  have hr1 : r = 1 := by
    have : ∀ r : ZMod 2, r ^ Fintype.card (Fin 3) = 1 → r = 1 := by decide
    exact this r hr
  rw [mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1]
  simp

omit [Finite G] in
theorem center_eq_bot_of_simple_types {K : Subgroup G}
    (h : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
      LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6))) :
    center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
  rcases h with h | h | h
  · obtain ⟨e⟩ := h
    exact center_eq_bot_of_mulEquiv e
      (alternatingGroup.center_eq_bot (by simp [Nat.card_eq_fintype_card]))
  · obtain ⟨e⟩ := nonempty_equiv_SL32_of_lieModel h
    exact center_eq_bot_of_mulEquiv e center_SL32_eq_bot
  · obtain ⟨e⟩ := h
    exact center_eq_bot_of_mulEquiv e
      (alternatingGroup.center_eq_bot (by simp [Nat.card_eq_fintype_card]))

omit [Finite G] in
theorem o2Z_le_pCoreOf_of_center {K : Subgroup G} (h : center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) :
    A6.o2Z K ≤ pCoreOf 2 K := by
  rintro _ ⟨y', hy', rfl⟩
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) y' = 1 := by
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) y' ∈ center (↥K ⧸ CFSG.pCore 2 ↥K) := hy'
    rw [h] at h2
    exact (mem_bot).1 h2
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact U3.coe_mem_pCoreOf_iff.2 h1

omit [Finite G] in
theorem o2Z_eq_inf_centralizer {K W : Subgroup G} (hKW : K ≤ normalizer (W : Set G))
    (hO : pCoreOf 2 K ≤ centralizer (W : Set G)) (hne : ¬ K ≤ centralizer (W : Set G))
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hcen : center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ ∨ center ↥(autOn K W) = ⊥) :
    A6.o2Z K = K ⊓ centralizer (W : Set G) := by
  refine le_antisymm (le_inf A6.o2Z_le_L fun y hy => ?_) ?_
  · rcases hcen with hc | hc
    · exact hO (o2Z_le_pCoreOf_of_center hc hy)
    · obtain ⟨hyK, hcomm⟩ := A6.mem_o2Z_iff.1 hy
      have ha : A6.autOnHom hKW ⟨y, hyK⟩ ∈ center ↥(autOn K W) := by
        rw [mem_center_iff]
        intro b
        obtain ⟨l, rfl⟩ := A6.autOnHom_surjective hKW b
        have hc1 : A6.autOnHom hKW (⟨y, hyK⟩ * l * (⟨y, hyK⟩ : ↥K)⁻¹ * l⁻¹) = 1 := by
          apply Subtype.ext
          rw [A6.autOnHom_apply]
          exact A1b.conjAct_eq_one_iff.2 (hO (hcomm l l.2))
        rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hc1
        calc A6.autOnHom hKW l * A6.autOnHom hKW ⟨y, hyK⟩ =
            (A6.autOnHom hKW ⟨y, hyK⟩ * A6.autOnHom hKW l * (A6.autOnHom hKW ⟨y, hyK⟩)⁻¹ *
              (A6.autOnHom hKW l)⁻¹)⁻¹ * (A6.autOnHom hKW ⟨y, hyK⟩ * A6.autOnHom hKW l) := by
              group
          _ = A6.autOnHom hKW ⟨y, hyK⟩ * A6.autOnHom hKW l := by rw [hc1, inv_one, one_mul]
      rw [hc, mem_bot] at ha
      have h1 := congrArg Subtype.val ha
      rw [A6.autOnHom_apply] at h1
      exact A1b.conjAct_eq_one_iff.1 h1
  · set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
    have hCn : ((K ⊓ centralizer (W : Set G)).subgroupOf K).Normal :=
      (normal_subgroupOf_iff_le_normalizer inf_le_left).2 fun l hl =>
        inf_normalizer_le_normalizer_inf
          ⟨le_normalizer hl, U3.mem_normalizer_centralizer_of (hKW hl)⟩
    have hNn : (((K ⊓ centralizer (W : Set G)).subgroupOf K).map π).Normal :=
      hCn.map π (QuotientGroup.mk'_surjective _)
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hNn with htop | hcen'
    · exfalso
      apply hne
      intro l hl
      have hl' : π ⟨l, hl⟩ ∈ ((K ⊓ centralizer (W : Set G)).subgroupOf K).map π :=
        htop ▸ mem_top _
      obtain ⟨c, hc, hcl⟩ := hl'
      have h1 : c⁻¹ * ⟨l, hl⟩ ∈ CFSG.pCore 2 ↥K := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        have : (QuotientGroup.mk c : ↥K ⧸ CFSG.pCore 2 ↥K) = QuotientGroup.mk ⟨l, hl⟩ := hcl
        rw [this, inv_mul_cancel]
      have h2 : ((c⁻¹ * ⟨l, hl⟩ : ↥K) : G) ∈ centralizer (W : Set G) :=
        hO (U3.coe_mem_pCoreOf_iff.2 h1)
      have h3 : (c : G) ∈ centralizer (W : Set G) := (mem_inf.1 (mem_subgroupOf.1 hc)).2
      have e : l = c * ((c⁻¹ * ⟨l, hl⟩ : ↥K) : G) := by simp
      rw [e]
      exact mul_mem h3 h2
    · intro x hx
      exact ⟨⟨x, hx.1⟩, hcen' ⟨⟨x, hx.1⟩, mem_subgroupOf.2 hx, rfl⟩, rfl⟩

omit [Finite G] in
theorem le_centralizer_of_sectionIso {X D V₀ J : Subgroup G} (hDX : D ≤ X)
    (hXV : X ≤ normalizer (V₀ : Set G)) (hXJ : X ≤ normalizer (J : Set G))
    (hJC : J ⊓ centralizer (X : Set G) = ⊥) (hDV : D ≤ centralizer (V₀ : Set G))
    (h : IsXSectionIso₂ X V₀ (V₀ ⊓ centralizer (X : Set G)) J (J ⊓ centralizer (X : Set G))) :
    D ≤ centralizer (J : Set G) := by
  obtain ⟨hn1, hn2, e, he⟩ := h
  intro d hd
  rw [mem_centralizer_iff]
  intro j hj
  obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (e.symm (QuotientGroup.mk (⟨j, hj⟩ : ↥J)))
  have hev : e (QuotientGroup.mk v) = QuotientGroup.mk (⟨j, hj⟩ : ↥J) := by
    rw [hv, MulEquiv.apply_symm_apply]
  have hv' : d * (v : G) * d⁻¹ ∈ V₀ := (mem_normalizer_iff.mp (hXV (hDX hd)) v).mp v.2
  have hj' : d * j * d⁻¹ ∈ J := (mem_normalizer_iff.mp (hXJ (hDX hd)) j).mp hj
  have h1 := he d (hDX hd) v ⟨j, hj⟩ hv' hj' hev
  have hvv : (⟨d * (v : G) * d⁻¹, hv'⟩ : ↥V₀) = v := by
    apply Subtype.ext
    show d * (v : G) * d⁻¹ = v
    rw [← mem_centralizer_iff.mp (hDV hd) v v.2, mul_inv_cancel_right]
  rw [hvv, hev, QuotientGroup.eq, mem_subgroupOf, hJC, mem_bot] at h1
  have h2 : j⁻¹ * (d * j * d⁻¹) = 1 := by simpa using h1
  have h3 : d * j * d⁻¹ = j := by
    calc d * j * d⁻¹ = j * (j⁻¹ * (d * j * d⁻¹)) := by group
      _ = j := by rw [h2, mul_one]
  calc j * d = d * j * d⁻¹ * d := by rw [h3]
    _ = d * j := by group

theorem o2Z_le_centralizer_R2 {T K H : Subgroup G} (hTsyl : IsSylowTwoOf T H)
    (hKH : K ≤ H) (hHK : H ≤ normalizer (K : Set G)) (hTKsyl : IsSylowTwoOf T (K ⊔ T))
    (hcharKT : CharTwo (K ⊔ T)) (h3 : ∀ y ∈ A6.o2Z K, y ^ 3 ∈ pCoreOf 2 K)
    (hirr : ∀ W : Subgroup G, IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T W →
      A6.o2Z K ≤ centralizer (W : Set G)) :
    A6.o2Z K ≤ centralizer (reducedAggregate H : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := reducedAggregate H with hUdef
  set D := A6.o2Z K with hDdef
  set R := reducedAggregate (K ⊔ T) with hRdef
  obtain ⟨-, hHU, hUe, -⟩ := twoReduced_R2 H
  have hOU := pCoreOf_le_centralizer_R2 H
  have hUT : U ≤ T :=
    (R2_le_pCoreOf H).trans (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTsyl)
  have hO2K : pCoreOf 2 K ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans hKH)
      (hHK.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
  have hDK : D ≤ K := A6.o2Z_le_L
  have hND : normalizer (K : Set G) ≤ normalizer (D : Set G) := A6.normalizer_L_le_o2Z
  have hTK : T ≤ normalizer (K : Set G) := hTsyl.1.trans hHK
  have hDU : D ≤ normalizer (U : Set G) := (hDK.trans hKH).trans hHU
  have h3U : ∀ y ∈ D, y ^ 3 ∈ centralizer (U : Set G) := fun y hy => hOU (hO2K (h3 y hy))
  have hcop : ⁅U, D⁆ ⊓ centralizer (D : Set G) = ⊥ :=
    U3.commutator_inf_centralizer_eq_bot_of hDU hUe h3U
  by_contra hDC
  have hW0 : ⁅U, D⁆ ≠ ⊥ := by
    intro h0
    apply hDC
    rw [commutator_eq_bot_iff_le_centralizer] at h0
    exact le_centralizer_iff.mp h0
  have hW0U : ⁅U, D⁆ ≤ U := by
    rw [commutator_le]
    intro u hu d hd
    rw [commutatorElement_def]
    have : d * u⁻¹ * d⁻¹ ∈ U := (mem_normalizer_iff.mp (hDU hd) _).mp (inv_mem hu)
    have e : u * d * u⁻¹ * d⁻¹ = u * (d * u⁻¹ * d⁻¹) := by group
    rw [e]
    exact mul_mem hu this
  have hKTN : K ⊔ T ≤ normalizer ((⁅U, D⁆ : Subgroup G) : Set G) := by
    refine sup_le (fun k hk => ?_) (fun t ht => ?_)
    · exact mem_normalizer_commutator (hHU (hKH hk)) (hND (le_normalizer hk))
    · exact mem_normalizer_commutator (hHU (hTsyl.1 ht)) (hND (hTK ht))
  obtain ⟨z, hz1⟩ := ne_bot_iff_exists_ne_one.mp (inf_centralizer_ne_bot_of_two hTsyl.2.1
    (hW0U.trans hUT) (le_sup_right.trans hKTN) hW0)
  have hzW : (z : G) ∈ ⁅U, D⁆ := (mem_inf.1 z.2).1
  have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzZ : (z : G) ∈ quasithinOmegaOneCenter T :=
    mem_quasithinOmegaOneCenter_iff.2 ⟨hUT (hW0U hzW), (mem_inf.1 z.2).2, hUe.2 _ (hW0U hzW)⟩
  set W₁ := conjClosure (zpowers (z : G)) (K ⊔ T) with hW₁def
  have hW₁R : W₁ ≤ R := le_R2_of_isTwoReducedIn
    (isTwoReducedIn_conjClosure_of_sylowIn hTKsyl.1 hTKsyl.2.1 hTKsyl.2.2 hcharKT
      (zpowers_le.mpr hzZ))
  have hW₁W : W₁ ≤ ⁅U, D⁆ := conjClosure_le fun g hg x hx =>
    (mem_normalizer_iff.mp (hKTN hg) x).mp ((zpowers_le.mpr hzW) hx)
  have hW₁K : K ≤ normalizer (W₁ : Set G) := le_sup_left.trans (le_normalizer_conjClosure _ _)
  have hW₁1 : W₁ ≠ ⊥ := by
    intro h
    have := le_conjClosure (zpowers (z : G)) (K ⊔ T) (mem_zpowers (z : G))
    rw [← hW₁def, h, mem_bot] at this
    exact hz1' this
  obtain ⟨J, hJ⟩ := (Set.toFinite {J : Subgroup G | J ≤ W₁ ∧ J ≠ ⊥ ∧
    K ≤ normalizer (J : Set G)}).exists_minimal ⟨W₁, le_rfl, hW₁1, hW₁K⟩
  obtain ⟨⟨hJW, hJ1, hKJ⟩, hJmin⟩ := hJ
  have hJD : J ⊓ centralizer (D : Set G) = ⊥ :=
    le_bot_iff.mp (hcop ▸ inf_le_inf_right _ (hJW.trans hW₁W))
  have hJC : J ⊓ centralizer (K : Set G) = ⊥ :=
    le_bot_iff.mp (hJD ▸ inf_le_inf_left _ (centralizer_le (SetLike.coe_subset_coe.mpr hDK)))
  have hJbase : IsIrrPlusBase K R J := by
    refine ⟨hJW.trans hW₁R, hJ1, hKJ, ?_, ?_, fun J' hJ'C hJ'J hKJ' => ?_⟩
    · have hle : ⁅J, K⁆ ≤ J := by
        rw [commutator_le]
        intro j hj k hk
        rw [commutatorElement_def]
        have : k * j⁻¹ * k⁻¹ ∈ J := (mem_normalizer_iff.mp (hKJ hk) _).mp (inv_mem hj)
        have e : j * k * j⁻¹ * k⁻¹ = j * (k * j⁻¹ * k⁻¹) := by group
        rw [e]
        exact mul_mem hj this
      refine le_antisymm hle (hJmin ⟨hle.trans hJW, fun h0 => hJ1 ?_, fun k hk =>
        mem_normalizer_commutator (hKJ hk) (le_normalizer hk)⟩ hle)
      rw [commutator_eq_bot_iff_le_centralizer] at h0
      rw [← hJC]
      exact (inf_eq_left.mpr h0).symm
    · rw [hJC]
      exact bot_lt_iff_ne_bot.mpr hJ1
    · by_cases h0 : J' = ⊥
      · exact Or.inl (h0.trans hJC.symm)
      · exact Or.inr (le_antisymm hJ'J (hJmin ⟨hJ'J.trans hJW, h0, hKJ'⟩ hJ'J))
  obtain ⟨-, hRN, hRe, -⟩ := twoReduced_R2 (K ⊔ T)
  have : IsMulCommutative ↥R := hRe.1
  obtain ⟨V₀, hV₀, hiso⟩ := exists_isIrrPlusIn_sectionIso hRe.2
    (le_sup_left.trans hRN) (le_sup_right.trans hRN) hTK hTsyl.2.1 hJbase
  have hDJ := le_centralizer_of_sectionIso hDK hV₀.2.2.1 hKJ hJC (hirr V₀ hV₀) hiso
  apply hJ1
  rw [← hJD]
  exact (inf_eq_left.mpr (le_centralizer_iff.mp hDJ)).symm

end CFSG.Quasithin.H13.NQS134
