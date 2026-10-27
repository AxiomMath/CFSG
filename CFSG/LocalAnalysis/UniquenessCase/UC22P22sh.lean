module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sg
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sf
public import CFSG.Milestones.ASVolI.B6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open
open CFSG.Quasithin (autI IntMod VZ ffJ fixV commV)
open scoped commutatorElement

@[expose] def NatSL2 {G : Type} [Group G] (L V : Subgroup G) (e : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ e ∧
    ∃ α : ↥L →* ↥(StatedSL 2 F), Function.Surjective α ∧
      α.ker = (L ⊓ centralizer (V : Set G)).subgroupOf L ∧
    ∃ β : ↥⁅V, L⁆ →* Multiplicative (Fin 2 → F), Function.Surjective β ∧
      β.ker = (⁅V, L⁆ ⊓ centralizer (L : Set G)).subgroupOf ⁅V, L⁆ ∧
      ∀ (l : ↥L) (u v : ↥⁅V, L⁆), (v : G) = l * u * l⁻¹ →
        Multiplicative.toAdd (β v) = (((α l : ↥(StatedSL 2 F)) : GL (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))

theorem isNaturalL2Prime_of_natSL2 {G : Type} [Group G] {L V : Subgroup G} {e : ℕ} (he : 1 < e)
    (hLN : L ≤ normalizer (V : Set G)) (h : NatSL2 L V e) : CFSG.Quasithin.IsNaturalL2Prime e L V := by
  obtain ⟨F, _, _, hF, α, hα, hαk, β, hβ, hβk, hβα⟩ := h
  exact Or.inl ⟨he, F, inferInstance, inferInstance, hF,
    ⟨fun l hl => CFSG.Quasithin.A4.mem_normalizer_commutator (hLN hl) (Subgroup.le_normalizer hl),
      α, hα, hαk, β, hβ, hβk, hβα⟩⟩

namespace P22s

section FFJ

variable {W : Type} [CommGroup W]

theorem le_normalizer_ffJ (X : Subgroup (MulAut W)) : X ≤ normalizer (ffJ X : Set (MulAut W)) := by
  refine le_normalizer_of_conj fun g hg j hj => ?_
  have hle : (ffJ X).map (MulAut.conj g).toMonoidHom ≤ ffJ X := by
    unfold CFSG.Quasithin.ffJ
    rw [Subgroup.map_iSup]
    refine iSup_le fun A => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hA => ?_
    rintro _ ⟨y, hy, rfl⟩
    have hmem : (MulAut.conj g).toMonoidHom y ∈ CFSG.Quasithin.B1.conjAut g A := by
      rw [CFSG.Quasithin.B1.mem_conjAut]
      simpa [MulAut.conj_apply, mul_assoc] using hy
    exact CFSG.Quasithin.B19.le_ffJ (X := X) (CFSG.Quasithin.B1.isFFStarOffender_conjAut hA hg) hmem
  have := hle ⟨j, hj, rfl⟩
  simpa [MulAut.conj_apply] using this

end FFJ

section AutI

variable {G : Type} [Group G] {V : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V)

theorem autI_le_normalizer_autI {K A : Subgroup G} (hKA : K ≤ normalizer (A : Set G)) :
    autI hV K ≤ normalizer (autI hV A : Set (MulAut (IntMod V hV))) := by
  refine le_normalizer_of_conj fun x hx y hy => ?_
  obtain ⟨g, hgK, rfl⟩ := (CFSG.Quasithin.mem_autI hV).1 hx
  obtain ⟨a, haA, rfl⟩ := (CFSG.Quasithin.mem_autI hV).1 hy
  refine (CFSG.Quasithin.mem_autI hV).2 ⟨g * a * g⁻¹, (mem_normalizer_iff.1 (hKA hgK) a).1 haA, ?_⟩
  simp only [map_mul, map_inv]

theorem isPGroup_autI {T : Subgroup G} (hT : IsPGroup 2 T) : IsPGroup 2 ↥(autI hV T) :=
  hT.comap_subtype.map _

theorem autI_le_normalizer_of_mod {K A : Subgroup G} (hAN : A ≤ normalizer (V : Set G))
    (h : ∀ g ∈ K, ∀ a ∈ A, ∃ a' ∈ A, g * a * g⁻¹ * a'⁻¹ ∈ centralizer (V : Set G)) :
    autI hV K ≤ normalizer (autI hV A : Set (MulAut (IntMod V hV))) := by
  refine le_normalizer_of_conj fun x hx y hy => ?_
  obtain ⟨g, hgK, rfl⟩ := (CFSG.Quasithin.mem_autI hV).1 hx
  obtain ⟨a, haA, rfl⟩ := (CFSG.Quasithin.mem_autI hV).1 hy
  obtain ⟨a', ha'A, hc⟩ := h g hgK a haA
  refine (CFSG.Quasithin.mem_autI hV).2 ⟨⟨a', hAN ha'A⟩, ha'A, ?_⟩
  have hgN := g.2
  set c : ↥(normalizer (V : Set G)) := g * a * g⁻¹ * ⟨a', hAN ha'A⟩⁻¹ with hcdef
  have hc1 : CFSG.Quasithin.convI hV c = 1 := (CFSG.Quasithin.convI_eq_one_iff hV c).2 hc
  have e : g * a * g⁻¹ = c * ⟨a', hAN ha'A⟩ := by rw [hcdef]; group
  rw [← map_inv, ← map_mul, ← map_mul, e, map_mul, hc1, one_mul]

@[expose] noncomputable def valHom : IntMod V hV →* G where
  toFun := IntMod.val
  map_one' := IntMod.val_one
  map_mul' := IntMod.val_mul

theorem commutator_eq_map_commV {L : Subgroup G} (hLN : L ≤ normalizer (V : Set G)) :
    ⁅V, L⁆ = (commV (autI hV L)).map (valHom hV) := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro v hv l hl
    set w : IntMod V hV := IntMod.mk hV ⟨v, hv⟩ with hw
    refine ⟨CFSG.Quasithin.convI hV ⟨l, hLN hl⟩ w⁻¹ * (w⁻¹)⁻¹,
      Subgroup.subset_closure ⟨_, CFSG.Quasithin.convI_mem_autI hV hl (hLN hl), w⁻¹, rfl⟩, ?_⟩
    change IntMod.val (CFSG.Quasithin.convI hV ⟨l, hLN hl⟩ w⁻¹ * (w⁻¹)⁻¹) = ⁅v, l⁆
    rw [IntMod.val_mul, CFSG.Quasithin.convI_apply_val, inv_inv, IntMod.val_inv]
    have hv' : w.val = v := rfl
    rw [hv', commutatorElement_def]
    have hc : l * v⁻¹ * l⁻¹ ∈ V := (mem_normalizer_iff.1 (hLN hl) v⁻¹).1 (V.inv_mem hv)
    have := CFSG.Open.IsElemAbelian.comm hV hc hv
    calc l * v⁻¹ * l⁻¹ * v = v * (l * v⁻¹ * l⁻¹) := this
      _ = v * l * v⁻¹ * l⁻¹ := by group
  · rw [Subgroup.map_le_iff_le_comap]
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨φ, hφ, v, rfl⟩ := hx
      obtain ⟨g, hgL, rfl⟩ := (CFSG.Quasithin.mem_autI hV).1 hφ
      change IntMod.val (CFSG.Quasithin.convI hV g v * v⁻¹) ∈ ⁅V, L⁆
      rw [IntMod.val_mul, CFSG.Quasithin.convI_apply_val, IntMod.val_inv, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hgL v.val_mem
    | one => exact Subgroup.one_mem _
    | mul x y _ _ hx hy => exact Subgroup.mul_mem _ hx hy
    | inv x _ hx => exact Subgroup.inv_mem _ hx

theorem mk_mem_commV {L : Subgroup G} (hLN : L ≤ normalizer (V : Set G)) {w : G} (hw : w ∈ ⁅V, L⁆)
    (hwV : w ∈ V) : IntMod.mk hV ⟨w, hwV⟩ ∈ commV (autI hV L) := by
  rw [commutator_eq_map_commV hV hLN] at hw
  obtain ⟨u, hu, huw⟩ := hw
  have : u = IntMod.mk hV ⟨w, hwV⟩ := IntMod.val_injective huw
  rwa [← this]

end AutI

section Binary

variable {G : Type} [Group G] [Finite G] {V : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V)

@[expose] noncomputable def secEval (A : Type) [CommGroup A] :
    ↥(⊤ : Subgroup A) ⧸ (⊥ : Subgroup A).subgroupOf ⊤ →* A :=
  QuotientGroup.lift _ (⊤ : Subgroup A).subtype fun x hx => by
    rw [Subgroup.bot_subgroupOf, Subgroup.mem_bot] at hx
    rw [hx, MonoidHom.mem_ker, map_one]

theorem secEval_mk {A : Type} [CommGroup A] (m : ↥(⊤ : Subgroup A)) :
    secEval A (QuotientGroup.mk m) = m := rfl

theorem secEval_injective {A : Type} [CommGroup A] : Function.Injective (secEval A) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro q hq
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  rw [MonoidHom.mem_ker, secEval_mk] at hq
  rw [Subgroup.mem_bot, show m = 1 from Subtype.ext hq]
  rfl

@[expose] noncomputable def toSec {L : Subgroup G} (hLN : L ≤ normalizer (V : Set G))
    (J : Subgroup (MulAut (IntMod V hV))) :
    ↥⁅V, L⁆ →* ↥(fixV J ⊔ commV (autI hV L)) where
  toFun w := ⟨IntMod.mk hV ⟨w, Subgroup.le_normalizer_iff_commutator_le_left.mp hLN w.2⟩,
    Subgroup.mem_sup_right (mk_mem_commV hV hLN w.2 _)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

end Binary

end P22s

open P22s

section Binary

variable {G : Type} [Group G] [Finite G] {V : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V)

theorem uc22p22sh_natural_of_binary {L : Subgroup G} (hLN : L ≤ normalizer (V : Set G))
    {J : Subgroup (MulAut (IntMod V hV))} (hLJ : autI hV L ≤ J)
    (hfix : ∀ w ∈ ⁅V, L⁆, w ∈ centralizer (L : Set G) → ∀ hw : w ∈ V, IntMod.mk hV ⟨w, hw⟩ ∈ fixV J)
    {e : ℕ} (hnat : CFSG.Quasithin.BinaryNaturalSL (autI hV L) (fixV J ⊔ commV (autI hV L)) (fixV J) 2 e) :
    NatSL2 L V e := by
  classical
  dsimp only [CFSG.Quasithin.BinaryNaturalSL, CFSG.Quasithin.FFModel.Realizes,
    CFSG.Quasithin.FFModel.RealizesVia, CFSG.Quasithin.FFModel.nat] at hnat
  obtain ⟨K, _, _, hK, π, hπs, -, -, -, -, -, -, β₀, hβ₀s, hβ₀1, hβ₀eq⟩ := hnat
  letI : Fintype K := Fintype.ofFinite K
  have hVL : ⁅V, L⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hLN
  have hπi : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro γ hγ
    rw [MonoidHom.mem_ker] at hγ
    have hfixm : ∀ x : Fin 2 → K,
        ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec x = x := by
      intro x
      obtain ⟨q, hq⟩ := hβ₀s (QuotientGroup.mk ⟨Multiplicative.ofAdd x, Subgroup.mem_top _⟩)
      have hqq : ((π γ : ↥(autI hV L)) : MulAut (IntMod V hV)) (q : IntMod V hV) = q := by
        rw [hγ]
        rfl
      have hu : ((π γ : ↥(autI hV L)) : MulAut (IntMod V hV)) (q : IntMod V hV) ∈
          fixV J ⊔ commV (autI hV L) := by
        rw [hqq]
        exact q.2
      have h1 := hβ₀eq γ q ⟨Multiplicative.ofAdd x, Subgroup.mem_top _⟩ hu (Subgroup.mem_top _) hq
      have h2 : (⟨((π γ : ↥(autI hV L)) : MulAut (IntMod V hV)) (q : IntMod V hV), hu⟩ :
          ↥(fixV J ⊔ commV (autI hV L))) = q := Subtype.ext hqq
      rw [h2, hq] at h1
      have h3 := congrArg (secEval (Multiplicative (Fin 2 → K))) h1
      rw [secEval_mk, secEval_mk] at h3
      exact (congrArg Multiplicative.toAdd h3).symm
    have hlin : Matrix.toLin' ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        Matrix.toLin' (1 : Matrix (Fin 2) (Fin 2) K) := by
      refine LinearMap.ext fun x => ?_
      rw [Matrix.toLin'_one, LinearMap.id_apply, Matrix.toLin'_apply]
      exact hfixm x
    have hmat := Matrix.toLin'.injective hlin
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Units.ext hmat)
  set e₀ : ↥(StatedSL 2 K) ≃* ↥(autI hV L) :=
    MulEquiv.ofBijective π (show Function.Bijective π from ⟨hπi, hπs⟩) with he₀
  set st : ↥L →* ↥(autI hV L) := CFSG.Quasithin.GE23.starHom hV hLN with hst
  refine ⟨K, inferInstance, inferInstance, by rw [← Nat.card_eq_fintype_card, hK],
    e₀.symm.toMonoidHom.comp st,
    e₀.symm.surjective.comp (CFSG.Quasithin.GE23.starHom_surjective hV hLN), ?_,
    (secEval (Multiplicative (Fin 2 → K))).comp (β₀.comp (toSec hV hLN J)), ?_, ?_, ?_⟩
  ·
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      ← MonoidHom.mem_ker, hst, CFSG.Quasithin.GE23.ker_starHom]
  ·
    intro x
    obtain ⟨u, hu⟩ := hβ₀s (QuotientGroup.mk ⟨x, Subgroup.mem_top _⟩)
    obtain ⟨z, hz, c, hc, hzc⟩ := Subgroup.mem_sup.1 u.2
    have hcV : (c.val : G) ∈ ⁅V, L⁆ := by
      rw [commutator_eq_map_commV hV hLN]
      exact ⟨c, hc, rfl⟩
    refine ⟨⟨c.val, hcV⟩, ?_⟩
    have hzβ : β₀ ⟨z, Subgroup.mem_sup_left hz⟩ = 1 := (hβ₀1 _).2 hz
    have hsplit : u = ⟨z, Subgroup.mem_sup_left hz⟩ * toSec hV hLN J ⟨c.val, hcV⟩ := by
      apply Subtype.ext
      rw [← hzc]
      rfl
    change secEval (Multiplicative (Fin 2 → K)) (β₀ (toSec hV hLN J ⟨c.val, hcV⟩)) = x
    rw [show β₀ (toSec hV hLN J ⟨c.val, hcV⟩) = β₀ u by rw [hsplit, map_mul, hzβ, one_mul], hu,
      secEval_mk]
  ·
    ext w
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf]
    constructor
    · intro hw
      have h1 : β₀ (toSec hV hLN J w) = 1 := secEval_injective (by rw [hw, map_one])
      have h2 := (hβ₀1 _).1 h1
      have h3 : IntMod.mk hV ⟨w, hVL w.2⟩ ∈ fixV (autI hV L) := fun x hx => h2 x (hLJ hx)
      exact ⟨w.2, (CFSG.Quasithin.mem_fixV_autI hV hLN _).1 h3⟩
    · rintro ⟨-, hwC⟩
      have h1 : β₀ (toSec hV hLN J w) = 1 := (hβ₀1 _).2 (hfix w w.2 hwC (hVL w.2))
      rw [h1, map_one]
  ·
    intro l u v huv
    set γ : ↥(StatedSL 2 K) := e₀.symm (st l) with hγ
    have hπγ : π γ = st l := by
      have h0 : e₀ γ = st l := e₀.apply_symm_apply _
      rwa [he₀, MulEquiv.ofBijective_apply] at h0
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β₀ (toSec hV hLN J u))
    have hconj : ((π γ : ↥(autI hV L)) : MulAut (IntMod V hV)) (toSec hV hLN J u : IntMod V hV) =
        (toSec hV hLN J v : IntMod V hV) := by
      apply IntMod.val_injective
      rw [hπγ, hst, CFSG.Quasithin.GE23.starHom_apply, CFSG.Quasithin.convHom_apply,
        CFSG.Quasithin.convI_apply_val]
      exact huv.symm
    have hu' : ((π γ : ↥(autI hV L)) : MulAut (IntMod V hV)) (toSec hV hLN J u : IntMod V hV) ∈
        fixV J ⊔ commV (autI hV L) := by
      rw [hconj]
      exact (toSec hV hLN J v).2
    have h1 := hβ₀eq γ (toSec hV hLN J u) m hu' (Subgroup.mem_top _) hm.symm
    have h2 : (⟨_, hu'⟩ : ↥(fixV J ⊔ commV (autI hV L))) = toSec hV hLN J v := Subtype.ext hconj
    rw [h2] at h1
    have hβu : secEval (Multiplicative (Fin 2 → K)) (β₀ (toSec hV hLN J u)) =
        (m : Multiplicative (Fin 2 → K)) := by
      rw [← hm, secEval_mk]
    change Multiplicative.toAdd (secEval (Multiplicative (Fin 2 → K)) (β₀ (toSec hV hLN J v))) =
      ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
        (Multiplicative.toAdd (secEval (Multiplicative (Fin 2 → K)) (β₀ (toSec hV hLN J u))))
    rw [h1, secEval_mk, hβu]
    rfl

end Binary

namespace P22s

theorem pCoreOf_le_of_isSubnormal {G : Type} [Group G] [Finite G] {A B : Subgroup G}
    (h : CFSG.Open.IsSubnormal A B) : pCoreOf 2 A ≤ pCoreOf 2 B := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction h with
  | refl A => exact le_rfl
  | @step A M B hAM hn _ ih =>
    refine le_trans ?_ ih
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 A).trans hAM) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 A)
    exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hAM).mp hn).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 A)

end P22s

open P22s

variable {G : Type} [Group G] [Finite G]

theorem uc22p22sh_natural (h69 : CFSG.ASVolI.B_6_9) (hTC : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    {D : Data G} {Ch : Choice2011 G} (h204 : S20_4 D) (hH : H1930 D) (c : Ctx22c D Ch)
    (hS7 : normalizer (proofS D : Set G) ≤ D.M) (hn3 : 3 ≤ c.n) {L : Subgroup G}
    (hLsub : CFSG.Open.IsSubnormal L (c.L0 ⊔ D.T)) (hLL0 : L ≤ c.L0) (hLp : ⁅L, L⁆ = L)
    (hLq : CFSG.Open.IsQuasisimple (Bar2 L))
    (hshape : IsSz (Bar2 L) c.n ∨ IsL2 (Bar2 L) c.n ∨ IsSU3 (Bar2 L) c.n ∨ IsSL3 (Bar2 L) c.n ∨
      IsSp4 (Bar2 L) c.n)
    (hnorm : ∀ g ∈ c.L0, ∀ l ∈ L, ∃ l' ∈ L, g * l * g⁻¹ * l'⁻¹ ∈
      centralizer (VZ D.T (c.L0 ⊔ D.T) : Set G))
    (hne : ¬ L ≤ centralizer (VZ D.T (c.L0 ⊔ D.T) : Set G)) :
    ∃ e : ℕ, 2 ≤ e ∧ NatSL2 L (VZ D.T (c.L0 ⊔ D.T)) e := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := c.L0 ⊔ D.T with hHdef
  set V₀ : Subgroup G := VZ D.T H with hV₀
  obtain ⟨hU, -, hFF, hred⟩ := uc22p22se_ffModule c hS7
  obtain ⟨hMP, hK, hO2⟩ := uc22p22se_b69_hyps hTC h204 hH c hU
  obtain ⟨-, s, Hs, hdir, -, hcomm, ⟨-, htrans⟩, hprod, h5⟩ :=
    h69 (IntMod V₀ hU) CFSG.Quasithin.IntMod.sq_eq_one (autI hU H) (autI hU D.T) (autI hU (H ⊓ D.M)) hMP hK
      hO2 hFF
  have hHN : H ≤ normalizer (V₀ : Set G) := hred.2.1
  have hL0N : c.L0 ≤ normalizer (V₀ : Set G) := le_sup_left.trans hHN
  have hLN : L ≤ normalizer (V₀ : Set G) := hLL0.trans hL0N
  have hL0H : H ≤ normalizer (c.L0 : Set G) := sup_le Subgroup.le_normalizer c.hL0.1.1
  have hO : pCoreOf 2 L ≤ centralizer (V₀ : Set G) := by
    refine (pCoreOf_le_of_isSubnormal hLsub).trans fun x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.1 ((uc22p22se_V0_facts c.toCtx21).1 hv).2 x hx).symm
  have hQH : autI hU c.L0 ≤ autI hU H := CFSG.Quasithin.autI_mono hU le_sup_left
  have hHQ : autI hU H ≤ normalizer (autI hU c.L0 : Set (MulAut (IntMod V₀ hU))) :=
    autI_le_normalizer_autI hU hL0H
  have hQp : ⁅autI hU c.L0, autI hU c.L0⁆ = autI hU c.L0 := uc22p22sg_autI_perfect hU hL0N c.hL0.1.2.1
  have hQ : autI hU c.L0 ≠ ⊥ := by
    rw [Ne, CFSG.Quasithin.autI_eq_bot_iff hU hL0N]
    exact fun h => hne (hLL0.trans h)
  have hfac : ∀ i, (∃ e : ℕ, 1 ≤ e ∧ Nonempty (↥(Hs i) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e))) ∨
      ∃ k : ℕ, Nonempty (↥(Hs i) ≃* Equiv.Perm (Fin (2 ^ k + 1))) := fun i =>
    (h5 i).imp (fun ⟨e, he, hψ, _, _⟩ => ⟨e, he, hψ⟩) (fun ⟨k, hψ, _, _⟩ => ⟨k, hψ⟩)
  obtain ⟨hQJ, hQeq, hD⟩ := uc22p22sf_structure (le_normalizer_ffJ _) hprod
    (isPGroup_autI hU D.sylowM.isPGroup) hdir htrans hfac hQH hHQ hQp hQ
  have hLne : autI hU L ≠ ⊥ := by
    rw [Ne, CFSG.Quasithin.autI_eq_bot_iff hU hLN]
    exact hne
  have hLq' := uc22p22sg_isQuasisimple_autI hU hLN hO hLq hLne
  obtain ⟨i, hi⟩ := uc22p22sf_eq_factor hdir hQJ hQeq (fun i => ⟨(hD i).1, (hD i).2.1, (hD i).2.2.1⟩)
    (CFSG.Quasithin.autI_mono hU hLL0) (autI_le_normalizer_of_mod hU hLN hnorm)
    (uc22p22sg_normal_of_isQuasisimple hLq') (uc22p22sg_autI_perfect hU hLN hLp) hLne
  rcases h5 i with ⟨e, he1, hψ, -, hnat⟩ | ⟨k, hψ, -, -⟩
  · obtain ⟨he2, hDi⟩ := (hD i).2.2.2.1 e he1 hψ
    have hLi : autI hU L = Hs i := hi.trans hDi
    refine ⟨e, he2, ?_⟩
    rw [← hLi] at hnat
    refine uc22p22sh_natural_of_binary hU hLN (hLi ▸ hdir.2.2 ▸ le_iSup Hs i) ?_ hnat
    intro w hw hwC hwV
    have hmk : IntMod.mk hU ⟨w, hwV⟩ ∈ commV (Hs i) := hLi ▸ mk_mem_commV hU hLN hw hwV
    have hfixi : IntMod.mk hU ⟨w, hwV⟩ ∈ fixV (Hs i) :=
      hLi ▸ (CFSG.Quasithin.mem_fixV_autI hU hLN _).2 hwC
    have hstab : ∀ j, Hs j ≤ MulAction.stabilizer (MulAut (IntMod V₀ hU)) (IntMod.mk hU ⟨w, hwV⟩) := by
      intro j x hx
      rw [MulAction.mem_stabilizer_iff]
      by_cases hji : j = i
      · subst hji
        exact hfixi x hx
      · have h1 := hcomm i j (Ne.symm hji)
        have h2 : x (IntMod.mk hU ⟨w, hwV⟩) * (IntMod.mk hU ⟨w, hwV⟩)⁻¹ ∈
            CFSG.Quasithin.commSub (commV (Hs i)) (Hs j) :=
          Subgroup.subset_closure ⟨x, hx, _, hmk, rfl⟩
        rw [h1, Subgroup.mem_bot, mul_inv_eq_one] at h2
        exact h2
    intro x hx
    have := (iSup_le hstab) (hdir.2.2.symm ▸ hx)
    exact this
  · exfalso
    obtain ⟨hk2, ⟨eA⟩⟩ := (hD i).2.2.2.2 k hψ
    have hm5 : 5 ≤ 2 ^ k + 1 := by
      have : 4 ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      omega
    exact uc22p22sg_not_alt_autI hU hLN hO hn3 hshape hm5 ((MulEquiv.subgroupCongr hi).trans eA)

end CFSG.LocalAnalysis.UniquenessCase.UC22
