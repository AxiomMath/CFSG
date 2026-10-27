module

public import CFSG.Quasithin.EmptyFaithful.S152He17D
public import CFSG.Quasithin.EmptyFaithful.S153QPD5
public import CFSG.Quasithin.EmptyFaithful.S153QPC7
public import CFSG.Quasithin.EmptyFaithful.S14610Hat6
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Main

public section

namespace CFSG.Quasithin.He17

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.He9
  CFSG.Quasithin.He16 CFSG.Quasithin.QP
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Algebra

theorem center_eq_bot_of_simple_card_sixty {N : Type*} [Group N] [IsSimpleGroup N] [Finite N]
    (hN : Nat.card N = 60) : Subgroup.center N = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center N) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : N, a * b = b * a := fun a b => by
      have : a ∈ Subgroup.center N := by rw [h]; trivial
      exact (Subgroup.mem_center_iff.1 this b).symm
    have hperf := isPerfect_of_simple_card_sixty (N := N) hN
    have h1 : (commutator N) = ⊥ := by
      rw [eq_bot_iff, commutator_def]
      refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (hcomm a b)
    have h2 := Group.isPerfect_def.1 hperf
    rw [h1] at h2
    have hsub : Subsingleton N := by
      refine ⟨fun a b => ?_⟩
      have ha : a ∈ (⊥ : Subgroup N) := by rw [h2]; trivial
      have hb : b ∈ (⊥ : Subgroup N) := by rw [h2]; trivial
      rw [Subgroup.mem_bot] at ha hb
      rw [ha, hb]
    have : Nat.card N = 1 := Nat.card_unique
    omega

theorem exists_factor {K H N : Type*} [Group K] [Group H] [Group N] (φ : K →* H) (ψ : K →* N)
    (hle : φ.ker ≤ ψ.ker) :
    ∃ θ : ↥φ.range →* N, (Function.Surjective ψ → Function.Surjective θ) ∧
      (IsPGroup 2 ψ.ker → IsPGroup 2 θ.ker) := by
  let e : (K ⧸ φ.ker) ≃* ↥φ.range := QuotientGroup.quotientKerEquivRange φ
  let θ : ↥φ.range →* N := (QuotientGroup.lift φ.ker ψ hle).comp e.symm.toMonoidHom
  have hθ : ∀ k : K, θ ⟨φ k, k, rfl⟩ = ψ k := by
    intro k
    have : e.symm ⟨φ k, k, rfl⟩ = (k : K ⧸ φ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show (QuotientGroup.lift φ.ker ψ hle) (e.symm ⟨φ k, k, rfl⟩) = ψ k
    rw [this]
    rfl
  refine ⟨θ, fun hs n => ?_, fun hk z => ?_⟩
  · obtain ⟨k, rfl⟩ := hs n
    exact ⟨⟨φ k, k, rfl⟩, hθ k⟩
  · obtain ⟨⟨_, k, rfl⟩, hz⟩ := z
    have hz' : θ ⟨φ k, k, rfl⟩ = 1 := hz
    rw [hθ] at hz'
    obtain ⟨j, hj⟩ := hk ⟨k, hz'⟩
    refine ⟨j, Subtype.ext (Subtype.ext ?_)⟩
    have h1 : k ^ 2 ^ j = 1 := congrArg Subtype.val hj
    show (φ k) ^ 2 ^ j = 1
    rw [← map_pow, h1, map_one]

omit [Finite G] in
theorem centralizer_of_actHom_eq_one {J V : Subgroup G} (hJV : J ≤ Subgroup.normalizer (V : Set G))
    (x : ↥J) (h : SBc17.actHom hJV x = 1) : (x : G) ∈ Subgroup.centralizer (V : Set G) := by
  have hca : conjAct V ⟨(x : G), hJV x.2⟩ = 1 :=
    congrArg (fun s : ↥(autOn J V) => (s : MulAut ↥V)) h
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have := congrArg (fun m : MulAut ↥V => ((m ⟨v, hv⟩ : ↥V) : G)) hca
  simp only [SBc17.conjAct_coe, MulAut.one_apply] at this
  calc v * (x : G) = ((x : G) * v * (x : G)⁻¹) * (x : G) := by rw [this]
    _ = (x : G) * v := by group

theorem commutator_Y_le {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5}
    (c : Ctx15204 T Mc M H K₁ K₂ π) :
    ⁅yOf152 T Mc M, yOf152 T Mc M⁆ ≤ pCoreOf 2 (yOf152 T Mc M) := by
  set Y := yOf152 T Mc M with hY
  set O := pCoreOf 2 Y with hO
  have hOY : O ≤ Y := pCoreOf_le 2 Y
  have hn : (O.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOY).2 (le_normalizer_pCoreOf 2 Y)
  have hcard : Nat.card (↥Y ⧸ O.subgroupOf Y) = 5 := by
    have := c.y.relIndex_five
    rw [hY, hO]
    exact this
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcyc : IsCyclic (↥Y ⧸ O.subgroupOf Y) := isCyclic_of_prime_card hcard
  let _ := IsCyclic.commGroup (α := ↥Y ⧸ O.subgroupOf Y)
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  have h1 : (QuotientGroup.mk (⟨a, ha⟩ : ↥Y) : ↥Y ⧸ O.subgroupOf Y) *
      QuotientGroup.mk (⟨b, hb⟩ : ↥Y) = QuotientGroup.mk (⟨b, hb⟩ : ↥Y) *
        QuotientGroup.mk (⟨a, ha⟩ : ↥Y) := mul_comm _ _
  have h2 : (⁅(⟨a, ha⟩ : ↥Y), ⟨b, hb⟩⁆ : ↥Y) ∈ O.subgroupOf Y := by
    have h3 : (QuotientGroup.mk' (O.subgroupOf Y)) ⁅(⟨a, ha⟩ : ↥Y), ⟨b, hb⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact h1
    exact (QuotientGroup.eq_one_iff _).1 h3
  exact h2

end Algebra

section Bridge

variable {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5}

theorem exists_lie_data (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (c : Ctx15204 T Mc M H K₁ K₂ π) {Lc : Subgroup G} (tail : Tail15204 c Lc)
    (hq : CFSG.IsQuasisimple ↥(modO2Image (g0Of T Mc M K₁) Lc)) :
    ∃ (Ŝ X : Subgroup ↥(autOn Lc (omegaOneCenterOf (pCoreOf 2 (Lc ⊔ rOf T Mc M K₁)))))
      (θ : ↥X →* ↥W5.A1), IsSylowTwoOf Ŝ ⊤ ∧ Ŝ ≤ Subgroup.normalizer (X : Set _) ∧
        Function.Surjective θ ∧ IsPGroup 2 θ.ker := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := rOf T Mc M K₁ with hR
  set V := omegaOneCenterOf (pCoreOf 2 (Lc ⊔ R)) with hV
  have hLG : Lc ≤ g0Of T Mc M K₁ := le_of_mem_cComp tail.comp
  have hNG : g0Of T Mc M K₁ ≤ Subgroup.normalizer (Lc : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLG).1 tail.normal
  have hRG : R ≤ g0Of T Mc M K₁ := tail.hyp.radical.1
  have hRN : R ≤ Subgroup.normalizer (Lc : Set G) := hRG.trans hNG
  obtain ⟨hJV, hD, -⟩ := SBc17.inner_facts (hC27 G) tail.hyp tail.comp
    (isQuasisimple_quot tail.comp hq) tail.charTwo tail.not_le hRN
  let φ : ↥K₁ →* ↥(autOn Lc V) := (SBc17.actHom hJV).comp (Subgroup.inclusion tail.le)
  let ψ : ↥K₁ →* ↥W5.A1 := WrH.psi₁ c.wr
  have hψs : Function.Surjective ψ := WrH.psi₁_surj c.wr
  have hψk : ψ.ker = CFSG.Open.pCore 2 ↥K₁ := WrH.psi₁_ker c.wr
  have hN60 : Nat.card ↥W5.A1 = 60 := W5.card_A1
  have _ := W5.A1_simple
  have hle : φ.ker ≤ ψ.ker := by
    intro k hk
    have hk1 : SBc17.actHom hJV ⟨(k : G), tail.le k.2⟩ = 1 := hk
    have hkc := centralizer_of_actHom_eq_one hJV ⟨(k : G), tail.le k.2⟩ hk1
    have hkZ : (k : G) ∈ oTwoZIn Lc := hD ⟨tail.le k.2, hkc⟩
    obtain ⟨-, hkcomm⟩ := mem_oTwoZIn_iff_commutator.mp hkZ
    let S₂ : Subgroup ↥K₁ := (pCoreOf 2 Lc).subgroupOf K₁
    have hS₂n : S₂.Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hn' : (n : G) ∈ pCoreOf 2 Lc := hn
      show ((g * n * g⁻¹ : ↥K₁) : G) ∈ pCoreOf 2 Lc
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Lc (tail.le g.2)) n).mp hn'
      simpa using this
    have hS₂p : IsPGroup 2 S₂ := by
      intro z
      obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 Lc ⟨(z : ↥K₁), z.2⟩
      refine ⟨j, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg (fun y : ↥(pCoreOf 2 Lc) => ((y : G))) hj
      simpa using this
    have hS₂le : S₂ ≤ ψ.ker := by
      rw [hψk]
      exact le_pCore 2 hS₂n hS₂p
    have hcomm : ∀ k' : ↥K₁, ψ k * ψ k' = ψ k' * ψ k := by
      intro k'
      have h1 : ⁅k, k'⁆ ∈ S₂ := by
        show ((⁅k, k'⁆ : ↥K₁) : G) ∈ pCoreOf 2 Lc
        simpa [commutatorElement_def] using hkcomm (k' : G) (tail.le k'.2)
      have h2 : ψ ⁅k, k'⁆ = 1 := hS₂le h1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
      exact h2
    have hcen : ψ k ∈ Subgroup.center ↥W5.A1 := by
      rw [Subgroup.mem_center_iff]
      intro n
      obtain ⟨k', rfl⟩ := hψs n
      exact (hcomm k').symm
    rw [center_eq_bot_of_simple_card_sixty hN60, Subgroup.mem_bot] at hcen
    exact hcen
  obtain ⟨θ, hθs, hθk⟩ := exists_factor φ ψ hle
  set S := sOf T K₁ with hS
  have hSyl : IsSylowTwoOf S (g0Of T Mc M K₁) := tail.sylow
  have hSL : IsSylowTwoOf (S ⊓ Lc) Lc :=
    CFSG.QuasithinUnique.L246C127.isSylowTwoOf_inf_of_isSubnormal'
      (subnormal_of_mem_cComp tail.comp) hSyl
  have hSp : IsPGroup 2 ((S ⊓ Lc).subgroupOf Lc) :=
    hSL.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSL.1).symm
  let Pl : Sylow 2 ↥Lc := hSp.toSylow hSL.2.2
  let Pk : Sylow 2 ↥(autOn Lc V) := Sylow.mapSurjective (SBc17.actHom_surjective hJV) Pl
  have hPk : (Pk : Subgroup ↥(autOn Lc V)) = ((S ⊓ Lc).subgroupOf Lc).map (SBc17.actHom hJV) :=
    Sylow.coe_mapSurjective _ Pl
  refine ⟨(Pk : Subgroup ↥(autOn Lc V)), φ.range, θ, isSylowTwoOf_top_of_sylow Pk, ?_, hθs hψs, hθk
    (hψk ▸ CFSG.LieType.BorelTits.pCore_isPGroup 2)⟩
  have hconj : ∀ s ∈ (Pk : Subgroup ↥(autOn Lc V)), ∀ h ∈ φ.range, s * h * s⁻¹ ∈ φ.range := by
    intro s hs h hh
    rw [hPk] at hs
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    obtain ⟨k, rfl⟩ := hh
    have hs₀S : ((s₀ : ↥Lc) : G) ∈ S := (Subgroup.mem_subgroupOf.mp hs₀).1
    have hsN : ((s₀ : ↥Lc) : G) ∈ Subgroup.normalizer (K₁ : Set G) := (inf_le_right :
      S ≤ Subgroup.normalizer (K₁ : Set G)) hs₀S
    have hk' : ((s₀ : ↥Lc) : G) * (k : G) * ((s₀ : ↥Lc) : G)⁻¹ ∈ K₁ :=
      (Subgroup.mem_normalizer_iff.mp hsN (k : G)).mp k.2
    refine ⟨⟨_, hk'⟩, ?_⟩
    show SBc17.actHom hJV (Subgroup.inclusion tail.le ⟨_, hk'⟩) =
      SBc17.actHom hJV s₀ * SBc17.actHom hJV (Subgroup.inclusion tail.le k) *
        (SBc17.actHom hJV s₀)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hconj s hs h hh, fun hh => ?_⟩
  have h3 := hconj s⁻¹ (inv_mem hs) _ hh
  have e : s⁻¹ * (s * h * s⁻¹) * s⁻¹⁻¹ = h := by group
  rwa [e] at h3

omit [Finite G] in
theorem false_of_c27_h (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    {G : Type} [Group G] [Finite G] {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5}
    (c : Ctx15204 T Mc M H K₁ K₂ π) {Lc : Subgroup G} (tail : Tail15204 c Lc)
    (hq : CFSG.IsQuasisimple ↥(modO2Image (g0Of T Mc M K₁) Lc))
    (hh : Nonempty (↥(autOn Lc (omegaOneCenterOf (pCoreOf 2 (Lc ⊔ rOf T Mc M K₁)))) ≃*
        ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))) ∨
      Nonempty (↥(autOn Lc (omegaOneCenterOf (pCoreOf 2 (Lc ⊔ rOf T Mc M K₁)))) ≃*
        ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)))) : False := by
  obtain ⟨Ŝ, X, θ, hŜ, hN, hθ, hk⟩ := exists_lie_data hC27 c tail hq
  have hN60 : Nat.card ↥W5.A1 = 60 := W5.card_A1
  have _ := W5.A1_simple
  have hF : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  rcases hh with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact false_of_sylow_normalizes_sl4 hF
      (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 (ZMod 2)).symm) hŜ hN
      hN60 θ hθ hk
  · exact false_of_sylow_normalizes_sl5 hF
      (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 5 (ZMod 2)).symm) hŜ hN
      hN60 θ hθ hk

theorem five_dvd_of_Y (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (c : Ctx15204 T Mc M H K₁ K₂ π) {Lc : Subgroup G} (tail : Tail15204 c Lc)
    (hYL : yOf152 T Mc M ≤ Lc) (hq : CFSG.IsQuasisimple ↥(modO2Image (g0Of T Mc M K₁) Lc))
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (e : ↥(autOn Lc (omegaOneCenterOf (pCoreOf 2 (Lc ⊔ rOf T Mc M K₁)))) ≃*
      Matrix.SpecialLinearGroup (Fin 3) F)
    (hmax : IsMaxParabolic2 (autOn Lc (omegaOneCenterOf (pCoreOf 2 (Lc ⊔ rOf T Mc M K₁))))
      (autOn ((M ⊓ g0Of T Mc M K₁) ⊓ Lc) (omegaOneCenterOf (pCoreOf 2 (Lc ⊔ rOf T Mc M K₁))))) :
    5 ∣ Nat.card F - 1 := by
  classical
  set R := rOf T Mc M K₁ with hR
  set V := omegaOneCenterOf (pCoreOf 2 (Lc ⊔ R)) with hV
  have hLG : Lc ≤ g0Of T Mc M K₁ := le_of_mem_cComp tail.comp
  have hNG : g0Of T Mc M K₁ ≤ Subgroup.normalizer (Lc : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLG).1 tail.normal
  have hRG : R ≤ g0Of T Mc M K₁ := tail.hyp.radical.1
  have hRN : R ≤ Subgroup.normalizer (Lc : Set G) := hRG.trans hNG
  obtain ⟨hJV, -, -⟩ := SBc17.inner_facts (hC27 G) tail.hyp tail.comp
    (isQuasisimple_quot tail.comp hq) tail.charTwo tail.not_le hRN
  obtain ⟨y, hyY, hyN, hy5⟩ := exists_five_element (hC27 G) c tail hYL hq
  set Y := yOf152 T Mc M with hY
  have hYM1 : Y ≤ (M ⊓ g0Of T Mc M K₁) ⊓ Lc := Y_le_inf c hYL
  have hYN : ∀ b ∈ (M ⊓ g0Of T Mc M K₁) ⊓ Lc, ∀ k ∈ Y, b * k * b⁻¹ ∈ Y := fun b hb k hk =>
    (Subgroup.mem_normalizer_iff.mp (c.y.normal hb.1.1) k).mp hk
  let π₁ := SBc17.actHom hJV
  let φ : ↥Lc →* Matrix.SpecialLinearGroup (Fin 3) F := e.toMonoidHom.comp π₁
  set Nh : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) := (Y.subgroupOf Lc).map φ with hNh
  have hP := isMaxParabolic2_top_of_mulEquiv hmax e
  set P : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) :=
    ((autOn ((M ⊓ g0Of T Mc M K₁) ⊓ Lc) V).subgroupOf (autOn Lc V)).map e.toMonoidHom with hPdef
  have hNP : Nh ≤ P := by
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨π₁ k, ?_, rfl⟩
    show ((π₁ k : ↥(autOn Lc V)) : MulAut ↥V) ∈ autOn ((M ⊓ g0Of T Mc M K₁) ⊓ Lc) V
    rw [SBc17.actHom_apply]
    exact SBc17.mem_autOn_iff.2 ⟨k, hJV k.2, hYM1 hk, rfl⟩
  have hnorm : ∀ p ∈ P, ∀ y' ∈ Nh, p * y' * p⁻¹ ∈ Nh := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨k, hk, rfl⟩
    have hs' : (s : MulAut ↥V) ∈ autOn ((M ⊓ g0Of T Mc M K₁) ⊓ Lc) V := hs
    obtain ⟨b, hbV, hb, hbs⟩ := SBc17.mem_autOn_iff.mp hs'
    have hbJ : b ∈ Lc := hb.2
    have hsπ : s = π₁ ⟨b, hbJ⟩ := Subtype.ext (by rw [SBc17.actHom_apply]; exact hbs.symm)
    refine ⟨⟨b, hbJ⟩ * k * ⟨b, hbJ⟩⁻¹, ?_, ?_⟩
    · show ((⟨b, hbJ⟩ * k * ⟨b, hbJ⟩⁻¹ : ↥Lc) : G) ∈ Y
      simpa using hYN b hb k hk
    · rw [hsπ]
      simp [φ]
  have hyL : y ∈ Lc := hYL hyY
  have hxN : φ ⟨y, hyL⟩ ∈ Nh := ⟨⟨y, hyL⟩, hyY, rfl⟩
  have hx5 : orderOf (φ ⟨y, hyL⟩) = 5 := by
    have h1 : orderOf (π₁ ⟨y, hyL⟩) = 5 := by
      rw [← Subgroup.orderOf_coe]
      exact hy5
    show orderOf (e (π₁ ⟨y, hyL⟩)) = 5
    rw [MulEquiv.orderOf_eq]
    exact h1
  have hshape : IsPGroup 2 ↥⁅Nh, Nh⁆ := by
    have hOY : pCoreOf 2 Y ≤ Lc := (pCoreOf_le 2 Y).trans hYL
    have hQp : IsPGroup 2 ↥((pCoreOf 2 Y).subgroupOf Lc) :=
      (pCoreOf_isPGroup 2 Y).of_equiv (Subgroup.subgroupOfEquivOfLe hOY).symm
    have hle : ⁅Y.subgroupOf Lc, Y.subgroupOf Lc⁆ ≤ (pCoreOf 2 Y).subgroupOf Lc := by
      refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      have := commutator_Y_le c (Subgroup.commutator_mem_commutator ha hb)
      simpa [commutatorElement_def, Subgroup.mem_subgroupOf] using this
    have h2 : IsPGroup 2 ↥⁅Y.subgroupOf Lc, Y.subgroupOf Lc⁆ := hQp.to_le hle
    have h3 : ⁅Nh, Nh⁆ = ⁅Y.subgroupOf Lc, Y.subgroupOf Lc⁆.map φ :=
      (Subgroup.map_commutator _ _ φ).symm
    rw [h3]
    exact h2.map φ
  exact QP.five_dvd_card_sub_one_of_normal_parabolic hP hNP hnorm hxN hx5 (Or.inl hshape)

omit [Finite G] in
theorem false_of_c27_g (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    {G : Type} [Group G] [Finite G] {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5}
    (c : Ctx15204 T Mc M H K₁ K₂ π) {Lc : Subgroup G} (tail : Tail15204 c Lc)
    (hYL : yOf152 T Mc M ≤ Lc) (hq : CFSG.IsQuasisimple ↥(modO2Image (g0Of T Mc M K₁) Lc))
    (hg : (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), 1 ≤ n ∧ Fintype.card F = 2 ^ n ∧
        Nonempty (↥(autOn Lc (omegaOneCenterOf (pCoreOf 2 (Lc ⊔ rOf T Mc M K₁)))) ≃*
          ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))) ∧
      IsMaxParabolic2 (autOn Lc (omegaOneCenterOf (pCoreOf 2 (Lc ⊔ rOf T Mc M K₁))))
        (autOn ((M ⊓ g0Of T Mc M K₁) ⊓ Lc) (omegaOneCenterOf (pCoreOf 2 (Lc ⊔ rOf T Mc M K₁)))) ∧
      IsMSPair (Lc ⊔ rOf T Mc M K₁) (rOf T Mc M K₁)) : False := by
  obtain ⟨⟨n, F, _, _, hn1, hcard, ⟨e⟩⟩, hmax, -⟩ := hg
  have : CharP F 2 := SBc17.charP_two_of_card_eq_pow hcard
  have : Finite F := Finite.of_fintype F
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hcard
  let e' := e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm
  have h5 : 5 ∣ Nat.card F - 1 := five_dvd_of_Y hC27 c tail hYL hq e' hmax
  have hn3 : 3 ≤ n := by
    by_contra hlt
    have hlt' : n < 3 := not_le.1 hlt
    rw [hFn] at h5
    interval_cases n <;> simp at h5
  obtain ⟨Ŝ, X, θ, hŜ, hN, hθ, hk⟩ := exists_lie_data hC27 c tail hq
  have hN60 : Nat.card ↥W5.A1 = 60 := W5.card_A1
  have _ := W5.A1_simple
  exact false_of_sylow_normalizes_sl3 hn3 hFn e' hŜ hN hN60 θ hθ hk

end Bridge

section Narrowing

@[expose] def C27Rest4 (M K V : Subgroup G) : Prop :=
  IsSp4Block K ∧ IsMaxParabolic2 (autOn K V) (autOn (M ⊓ K) V)

@[expose] def Input15204QuasiRest4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M H K₁ K₂ : Subgroup G) (π : ↥H →* W5)
    (c : Ctx15204 T Mc M H K₁ K₂ π) (Lc : Subgroup G), Tail15204 c Lc →
    yOf152 T Mc M ≤ Lc → ¬ IsSylowTwoOf (rOf T Mc M K₁) (rOf T Mc M K₁ ⊔ Lc) →
    CFSG.IsQuasisimple ↥(modO2Image (g0Of T Mc M K₁) Lc) →
    C27Rest4 (M ⊓ g0Of T Mc M K₁) Lc
      (omegaOneCenterOf (pCoreOf 2 (Lc ⊔ rOf T Mc M K₁))) → False

theorem input15204QuasiRest3_of_rest4
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G) (h : Input15204QuasiRest4) :
    Input15204QuasiRest3 := by
  intro G _ _ T Mc M H K₁ K₂ π c Lc tail hYL hnot hq hrest
  rcases hrest with he | hg | hh
  · exact h G T Mc M H K₁ K₂ π c Lc tail hYL hnot hq he
  · exact false_of_c27_g hC27 c tail hYL hq hg
  · exact false_of_c27_h hC27 c tail hq hh.1

end Narrowing

end CFSG.Quasithin.He17
