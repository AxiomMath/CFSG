module

public import CFSG.Quasithin.MS93.S510Tv
public import CFSG.Quasithin.MS93.S59Gen
public import CFSG.Quasithin.MS93.S5B58Sp

public noncomputable section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Pointwise Matrix

namespace S59

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

section NatM

theorem conj_mem_uq (h : PUHyp M T L) {m : G} (hm : m ∈ M) {u : G} (hu : u ∈ Uq M T L) :
    m * u * m⁻¹ ∈ Uq M T L :=
  (Subgroup.mem_normalizer_iff.1 (le_normalizer_Uq h.le_normalizer hm) u).1 hu

omit [Fintype F] in
theorem comm_of_fix (h : PUHyp M T L)
    (hlift : ∀ m ∈ M, ∀ u ∈ Uq M T L, m * u * m⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) →
      m * u * m⁻¹ = u)
    (c : MSP.NatCoord M (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) a)
    {m : G} (hm : m ∈ M) (u : ↥(Uq M T L))
    (hfix : MSP.mat (a ⟨m, hm⟩) *ᵥ c.vec u = c.vec u) : m * u = u * m := by
  have hconj := conj_mem_uq h hm u.2
  have hv := c.vec_commutator ⟨m, hm⟩ u hconj
  rw [hfix, sub_self] at hv
  have h0 := (c.vec_eq_zero_iff _).1 hv
  have h1 := hlift m hm u u.2 h0.2
  calc m * u = m * u * m⁻¹ * m := by group
    _ = u * m := by rw [h1]

omit [Fintype F] in
theorem fix_of_comm (h : PUHyp M T L)
    (c : MSP.NatCoord M (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) a)
    {m : G} (hm : m ∈ M) (u : ↥(Uq M T L)) (hmu : m * u = u * m) :
    MSP.mat (a ⟨m, hm⟩) *ᵥ c.vec u = c.vec u := by
  have hconj := conj_mem_uq h hm u.2
  have e : (⟨m * u * m⁻¹, hconj⟩ : ↥(Uq M T L)) = u := by
    apply Subtype.ext
    show m * u * m⁻¹ = u
    rw [hmu, mul_inv_cancel_right]
  have hc := c.vec_conj ⟨m, hm⟩ u hconj
  have e' : c.vec ⟨m * u * m⁻¹, hconj⟩ = c.vec u := by rw [e]
  exact hc.symm.trans e'

theorem mem_centralizer_of_comm_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E : Subgroup G} (hEM : E ≤ M)
    (hrel : (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) = 2 ^ k)
    {u : G} (hu : u ∈ ⁅Uq M T L, E⁆) (huL : u ∉ Subgroup.centralizer (L : Set G))
    {m : G} (hm : m ∈ M) (hmu : m * u = u * m) :
    m ∈ Subgroup.centralizer ((⁅Uq M T L, E⁆ : Subgroup G) : Set G) := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have hUE : ⁅Uq M T L, E⁆ ≤ Uq M T L :=
    commutator_le_left_of_le_normalizer (hEM.trans (le_normalizer_Uq h.le_normalizer))
  obtain ⟨p, hp, hcomm, -, -⟩ := S510.exists_point_of_relIndex h hd hEM hrel
  have hvp : ∀ x : ↥(Uq M T L), (x : G) ∈ ⁅Uq M T L, E⁆ → c.vec x ∈ p := fun x hx =>
    hcomm ▸ S5B.vec_mem_commSp h c hEM x hx
  set u' : ↥(Uq M T L) := ⟨u, hUE hu⟩
  have hv0 : c.vec u' ≠ 0 := fun h0 => huL ((c.vec_eq_zero_iff u').1 h0).2
  have hpv : p = F ∙ c.vec u' :=
    eq_span_singleton_of_mem_of_finrank_eq_one hp (hvp u' hu) hv0
  have hmv := fix_of_comm h c hm u' hmu
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  set x' : ↥(Uq M T L) := ⟨x, hUE hx⟩
  have hx' : c.vec x' ∈ F ∙ c.vec u' := hpv ▸ hvp x' hx
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hx'
  have hfix : MSP.mat (a ⟨m, hm⟩) *ᵥ c.vec x' = c.vec x' := by
    rw [← hr, Matrix.mulVec_smul, hmv]
  exact (comm_of_fix h hlift c hm x' hfix).symm

theorem mem_centralizer_of_normalizer_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E : Subgroup G} (hEM : E ≤ M)
    (hrel : (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) = 2 ^ k)
    {t : G} (htM : t ∈ M) {n : ℕ} (ht2 : t ^ 2 ^ n = 1) (htE : ∀ e ∈ E, t * e * t⁻¹ ∈ E) :
    t ∈ Subgroup.centralizer ((⁅Uq M T L, E⁆ : Subgroup G) : Set G) := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have : CharP F 2 := S5B.charP_two_of_card hd.2.1
  have hUE : ⁅Uq M T L, E⁆ ≤ Uq M T L :=
    commutator_le_left_of_le_normalizer (hEM.trans (le_normalizer_Uq h.le_normalizer))
  obtain ⟨p, hp, hcomm, -, -⟩ := S510.exists_point_of_relIndex h hd hEM hrel
  set Ē := (E.subgroupOf M).map a with hĒdef
  set at' := a ⟨t, htM⟩ with hat'
  have hinv : ∀ w ∈ MSP.commSp Ē, MSP.mat at' *ᵥ w ∈ MSP.commSp Ē := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨g, hg, v, rfl⟩ := hw
      obtain ⟨e, he, rfl⟩ := hg
      have hte : t * (e : G) * t⁻¹ ∈ E := htE _ (Subgroup.mem_subgroupOf.1 he)
      have hmem : a ⟨t * (e : G) * t⁻¹, hEM hte⟩ ∈ Ē :=
        ⟨⟨_, hEM hte⟩, Subgroup.mem_subgroupOf.2 hte, rfl⟩
      have e1 : (⟨t * (e : G) * t⁻¹, hEM hte⟩ : ↥M) = ⟨t, htM⟩ * e * ⟨t, htM⟩⁻¹ :=
        Subtype.ext rfl
      have key : MSP.mat at' *ᵥ (MSP.mat (a e) *ᵥ v - v) =
          MSP.mat (a ⟨t * (e : G) * t⁻¹, hEM hte⟩) *ᵥ (MSP.mat at' *ᵥ v) - MSP.mat at' *ᵥ v := by
        rw [e1, map_mul, map_mul, map_inv, Matrix.mulVec_sub, MSP.mat_mul_mulVec,
          MSP.mat_mul_mulVec, MSP.mat_inv_mulVec, hat']
      rw [key]
      exact MSP.sub_mem_commSp hmem _
    | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
    | smul r x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ r hx
  obtain ⟨x₀, hx₀, hpx⟩ := MSP.exists_eq_span_of_isPoint hp
  have hx₀p : x₀ ∈ MSP.commSp Ē := by rw [hcomm, hpx]; exact Submodule.mem_span_singleton_self _
  have hy : MSP.mat at' *ᵥ x₀ ∈ F ∙ x₀ := by rw [← hpx, ← hcomm]; exact hinv x₀ hx₀p
  have hy0 : MSP.mat at' *ᵥ x₀ ≠ 0 := mulVec_ne_zero at' hx₀
  have hspan : F ∙ (MSP.mat at' *ᵥ x₀) = F ∙ x₀ :=
    Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 hy)
      (by rw [finrank_span_singleton hy0, finrank_span_singleton hx₀])
  have hpow : at' ^ 2 ^ n = 1 := by
    rw [hat', ← map_pow]
    have : (⟨t, htM⟩ : ↥M) ^ 2 ^ n = 1 := Subtype.ext (by simpa using ht2)
    rw [this, map_one]
  have hfx := mulVec_eq_of_span_eq hpow hx₀ hspan
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  set x' : ↥(Uq M T L) := ⟨x, hUE hx⟩
  have hx' : c.vec x' ∈ F ∙ x₀ := by rw [← hpx, ← hcomm]; exact S5B.vec_mem_commSp h c hEM x' hx
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hx'
  have hfix : MSP.mat (a ⟨t, htM⟩) *ᵥ c.vec x' = c.vec x' := by
    rw [← hr, Matrix.mulVec_smul, ← hat', hfx]
  exact (comm_of_fix h hlift c htM x' hfix).symm

theorem centralizer_sup_eq_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {u : G} (hu : u ∈ Uq M T L) (huL : u ∉ Subgroup.centralizer (L : Set G))
    {E : Subgroup G} (hEM : E ≤ M) (hE2 : IsPGroup 2 E) {e : G} (he : e ∈ E)
    (heu : e * u ≠ u * e) :
    M ⊓ Subgroup.centralizer ({u} : Set G) ⊔ E = M := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have : CharP F 2 := S5B.charP_two_of_card hd.2.1
  set u' : ↥(Uq M T L) := ⟨u, hu⟩
  have hv0 : c.vec u' ≠ 0 := fun h0 => huL ((c.vec_eq_zero_iff u').1 h0).2
  set Ē := (E.subgroupOf M).map a with hĒdef
  have hĒ2 : IsPGroup 2 Ē :=
    (hE2.comap_of_injective M.subtype (Subgroup.subtype_injective M)).map a
  have hev : MSP.mat (a ⟨e, hEM he⟩) *ᵥ c.vec u' ≠ c.vec u' := fun hfix =>
    heu (comm_of_fix h hlift c (hEM he) u' hfix)
  have hgen := fixer_span_sup_eq_top hv0 hĒ2 ⟨⟨e, hEM he⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩ hev
  refine le_antisymm (sup_le inf_le_left hEM) ?_
  set K := M ⊓ Subgroup.centralizer ({u} : Set G) ⊔ E with hKdef
  have hfixK : ∀ m (hm : m ∈ M), MSP.mat (a ⟨m, hm⟩) *ᵥ c.vec u' = c.vec u' → m ∈ K :=
    fun m hm hfix => Subgroup.mem_sup_left ⟨hm, Subgroup.mem_centralizer_singleton_iff.2
      (comm_of_fix h hlift c hm u' hfix)⟩
  have himg : (K.subgroupOf M).map a = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine sup_le ?_ ?_
    · intro g hg
      obtain ⟨m, rfl⟩ := hd.2.2.1 g
      refine ⟨m, Subgroup.mem_subgroupOf.2 (hfixK m m.2 ?_), rfl⟩
      exact hg _ (Submodule.mem_span_singleton_self _)
    · rintro _ ⟨e', he', rfl⟩
      exact ⟨e', Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right
        (Subgroup.mem_subgroupOf.1 he')), rfl⟩
  intro m hm
  have hm' : a ⟨m, hm⟩ ∈ (K.subgroupOf M).map a := himg ▸ Subgroup.mem_top _
  obtain ⟨k', hk', hk'e⟩ := hm'
  have hker : a (k'⁻¹ * ⟨m, hm⟩) = 1 := by rw [map_mul, map_inv, hk'e, inv_mul_cancel]
  have hmk : ((k'⁻¹ * ⟨m, hm⟩ : ↥M) : G) ∈ K := by
    refine hfixK _ (k'⁻¹ * ⟨m, hm⟩).2 ?_
    rw [show (⟨((k'⁻¹ * ⟨m, hm⟩ : ↥M) : G), (k'⁻¹ * ⟨m, hm⟩).2⟩ : ↥M) = k'⁻¹ * ⟨m, hm⟩ from rfl,
      hker, MSP.mat_one, Matrix.one_mulVec]
  have : m = (k' : G) * ((k'⁻¹ * ⟨m, hm⟩ : ↥M) : G) := by simp
  rw [this]
  exact mul_mem (Subgroup.mem_subgroupOf.1 hk') hmk

theorem exists_conj_not_comm_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {u : G} (hu : u ∈ Uq M T L) (huL : u ∉ Subgroup.centralizer (L : Set G))
    {E : Subgroup G} (hEM : E ≤ M) (hE2 : IsPGroup 2 E) (hEO : ¬ E ≤ pCoreOf 2 M) :
    ∃ m ∈ M, ∃ e ∈ E, e * (m * u * m⁻¹) ≠ (m * u * m⁻¹) * e := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  obtain ⟨e, he, heO⟩ := Set.not_subset.1 hEO
  have hae : a ⟨e, hEM he⟩ ≠ 1 := by
    intro h1
    obtain ⟨n, hn⟩ := hE2 ⟨e, he⟩
    exact heO (S5B.mem_pCoreOf_of_ker h hd h1 ⟨n, by simpa using congrArg Subtype.val hn⟩)
  obtain ⟨w, hw⟩ : ∃ w : MSP.V4 F, MSP.mat (a ⟨e, hEM he⟩) *ᵥ w ≠ w := by
    by_contra hcon
    push Not at hcon
    exact hae (S5B.eq_one_of_fixVec_eq_top (eq_top_iff.2 fun w _ => S5B.mem_fixVec.2 (hcon w)))
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [Matrix.mulVec_zero] at hw
    exact hw rfl
  set u' : ↥(Uq M T L) := ⟨u, hu⟩
  have hv0 : c.vec u' ≠ 0 := fun h0 => huL ((c.vec_eq_zero_iff u').1 h0).2
  obtain ⟨g, hg⟩ := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.exists_statedSp_map_eq
    (MSP.isTotallyIsotropic_span (c.vec u')) (MSP.isTotallyIsotropic_span w)
    (by rw [finrank_span_singleton hv0, finrank_span_singleton hw0])
  have hgv : F ∙ (MSP.mat g *ᵥ c.vec u') = F ∙ w := by
    rw [← span_map_mat]
    exact hg
  have hgw : MSP.mat g *ᵥ c.vec u' ∈ F ∙ w := by
    rw [← hgv]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hgw
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hr
    exact mulVec_ne_zero g hv0 hr.symm
  obtain ⟨m, hm⟩ := hd.2.2.1 g
  have hconj := conj_mem_uq h m.2 hu
  refine ⟨m, m.2, e, he, fun hcomm => hw ?_⟩
  have hfix := fix_of_comm h c (hEM he) ⟨_, hconj⟩ hcomm
  have hvc := c.vec_conj m u' hconj
  have e1 : c.vec ⟨(m : G) * u * (m : G)⁻¹, hconj⟩ = r • w := by
    rw [hvc, hm, ← hr]
  rw [e1, Matrix.mulVec_smul] at hfix
  exact smul_right_injective _ hr0 hfix

theorem eq_one_or_eq_of_card_two {Γ : Type*} [Group Γ] {K : Subgroup Γ} (hK : Nat.card K = 2)
    {x y : Γ} (hx : x ∈ K) (hy : y ∈ K) (hy1 : y ≠ 1) : x = 1 ∨ x = y := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Fintype K := Fintype.ofFinite K
  by_contra hcon
  push Not at hcon
  have hs : ({(⟨1, one_mem K⟩ : K), (⟨x, hx⟩ : K), (⟨y, hy⟩ : K)} : Finset K).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · intro he
      exact hcon.2 (congrArg Subtype.val he)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun he => hcon.1 (congrArg Subtype.val he).symm,
        fun he => hy1 (congrArg Subtype.val he).symm⟩
  have h3 : 3 ≤ Nat.card K := by
    rw [← Fintype.card_eq_nat_card, ← hs]
    exact Finset.card_le_univ _
  omega

theorem card_commutator_le_two_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) (hk : k = 1)
    {E : Subgroup G} (hEM : E ≤ M)
    (hrel : (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) = 2 ^ k) :
    Nat.card ↥⁅Uq M T L, E⁆ ≤ 2 := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  obtain ⟨p, hp, -, -, hX⟩ := S510.exists_point_of_relIndex h hd hEM hrel
  have hFq : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hd.2.1, hk, pow_one]
  have hXc : Nat.card (MSP.xPoint p) = 2 := by rw [MSP.card_xPoint hp, hFq]
  have hcommU : ∀ x ∈ Uq M T L, ∀ y ∈ Uq M T L, x * y = y * x :=
    (isMulCommutative_subgroup_iff).1 h.isElemAbelian_Uq.1
  have hker : ∀ m (hm : m ∈ M), a ⟨m, hm⟩ = 1 → ∀ x ∈ Uq M T L, m * x = x * m := by
    intro m hm h1 x hx
    exact comm_of_fix h hlift c hm ⟨x, hx⟩ (by rw [h1, MSP.mat_one, Matrix.one_mulVec])
  by_cases hall : ∀ e (he : e ∈ E), a ⟨e, hEM he⟩ = 1
  · have hbot : ⁅Uq M T L, E⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro x hx e he
      rw [Subgroup.mem_bot, commutatorElement_def, ← hker e (hEM he) (hall e he) x hx]
      group
    rw [hbot, Subgroup.card_bot]
    norm_num
  push Not at hall
  obtain ⟨e₀, he₀, hae₀⟩ := hall
  have he₀M := hEM he₀
  have hmemX : ∀ e (he : e ∈ E), a ⟨e, hEM he⟩ ∈ MSP.xPoint p := fun e he =>
    hX ⟨⟨e, hEM he⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩
  let φ : ↥(Uq M T L) →* ↥(Uq M T L) :=
    { toFun := fun x => ⟨e₀ * x * e₀⁻¹ * (x : G)⁻¹,
        mul_mem (conj_mem_uq h he₀M x.2) (inv_mem x.2)⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        simp only [MulMemClass.coe_mul]
        have hx := x.2
        have hy := y.2
        have h1 := hcommU _ (conj_mem_uq h he₀M hy) _ (inv_mem hx)
        have h2 := hcommU _ (inv_mem hy) _ (inv_mem hx)
        calc e₀ * (x * y) * e₀⁻¹ * ((x : G) * y)⁻¹
            = e₀ * x * y * e₀⁻¹ * ((y : G)⁻¹ * (x : G)⁻¹) := by group
          _ = e₀ * x * y * e₀⁻¹ * ((x : G)⁻¹ * (y : G)⁻¹) := by rw [h2]
          _ = e₀ * x * e₀⁻¹ * ((e₀ * y * e₀⁻¹) * (x : G)⁻¹) * (y : G)⁻¹ := by group
          _ = e₀ * x * e₀⁻¹ * ((x : G)⁻¹ * (e₀ * y * e₀⁻¹)) * (y : G)⁻¹ := by rw [h1]
          _ = e₀ * x * e₀⁻¹ * (x : G)⁻¹ * (e₀ * y * e₀⁻¹ * (y : G)⁻¹) := by group }
  have hle : ⁅Uq M T L, E⁆ ≤ φ.range.map (Uq M T L).subtype := by
    rw [Subgroup.commutator_le]
    intro x hx e he
    rcases eq_one_or_eq_of_card_two hXc (hmemX e he) (hmemX e₀ he₀) hae₀ with h1 | h2
    · have : ⁅x, e⁆ = 1 := by
        rw [commutatorElement_def, ← hker e (hEM he) h1 x hx]
        group
      rw [this]
      exact one_mem _
    ·
      have hk1 : a ⟨e₀⁻¹ * e, mul_mem (inv_mem he₀M) (hEM he)⟩ = 1 := by
        have : (⟨e₀⁻¹ * e, mul_mem (inv_mem he₀M) (hEM he)⟩ : ↥M) =
            (⟨e₀, he₀M⟩ : ↥M)⁻¹ * ⟨e, hEM he⟩ := Subtype.ext rfl
        rw [this, map_mul, map_inv, h2, inv_mul_cancel]
      have hxinv := inv_mem hx
      have hc := hker _ _ hk1 x⁻¹ hxinv
      have hconj : e * x⁻¹ * e⁻¹ = e₀ * x⁻¹ * e₀⁻¹ := by
        calc e * x⁻¹ * e⁻¹ = e₀ * ((e₀⁻¹ * e) * x⁻¹) * e⁻¹ := by group
          _ = e₀ * (x⁻¹ * (e₀⁻¹ * e)) * e⁻¹ := by rw [hc]
          _ = e₀ * x⁻¹ * e₀⁻¹ := by group
      refine ⟨φ ⟨x⁻¹, hxinv⟩, ⟨⟨x⁻¹, hxinv⟩, rfl⟩, ?_⟩
      show e₀ * x⁻¹ * e₀⁻¹ * x⁻¹⁻¹ = ⁅x, e⁆
      have h3 := hcommU _ hx _ (conj_mem_uq h he₀M hxinv)
      rw [commutatorElement_def, inv_inv]
      calc e₀ * x⁻¹ * e₀⁻¹ * x = x * (e₀ * x⁻¹ * e₀⁻¹) := h3.symm
        _ = x * (e * x⁻¹ * e⁻¹) := by rw [hconj]
        _ = x * e * x⁻¹ * e⁻¹ := by group
  have hkerφ : (Subgroup.centralizer (E : Set G)).subgroupOf (Uq M T L) ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    have hx' := Subgroup.mem_subgroupOf.1 hx
    have : e₀ * x = x * e₀ := Subgroup.mem_centralizer_iff.1 hx' e₀ he₀
    show e₀ * x * e₀⁻¹ * (x : G)⁻¹ = 1
    rw [this]
    group
  have hfin : (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) ≠ 0 := by
    rw [hrel]
    positivity
  have hidx : φ.ker.index ≤ 2 := by
    have hdvd := Subgroup.index_dvd_of_le hkerφ
    have h2 : ((Subgroup.centralizer (E : Set G)).subgroupOf (Uq M T L)).index = 2 := by
      rw [← Subgroup.relIndex, hrel, hk, pow_one]
    rw [h2] at hdvd
    exact Nat.le_of_dvd (by norm_num) hdvd
  calc Nat.card ↥⁅Uq M T L, E⁆ ≤ Nat.card (φ.range.map (Uq M T L).subtype) :=
        Subgroup.card_le_of_le hle
    _ = Nat.card φ.range := Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    _ = φ.ker.index := (Subgroup.index_ker φ).symm
    _ ≤ 2 := hidx

end NatM

section Transport

omit [Finite G] [Fintype F] in
theorem mem_map_conj_imM (hTM : T ≤ M) {K : Subgroup G} {g x : (puAmalgam hTM).Universal} :
    x ∈ (imM hTM K).map (MulAut.conj g).toMonoidHom ↔
      ∃ x₀ : ↥M, (x₀ : G) ∈ K ∧ x = g * (puAmalgam hTM).ofA x₀ * g⁻¹ := by
  constructor
  · rintro ⟨_, ⟨x₀, hx₀, rfl⟩, rfl⟩
    exact ⟨x₀, Subgroup.mem_subgroupOf.1 hx₀, rfl⟩
  · rintro ⟨x₀, hx₀, rfl⟩
    exact ⟨_, ⟨x₀, Subgroup.mem_subgroupOf.2 hx₀, rfl⟩, rfl⟩

omit [Finite G] [Fintype F] in
theorem conj_ofA_comm_iff (hTM : T ≤ M) {g : (puAmalgam hTM).Universal} {x₀ y₀ : ↥M} :
    (g * (puAmalgam hTM).ofA x₀ * g⁻¹) * (g * (puAmalgam hTM).ofA y₀ * g⁻¹) =
      (g * (puAmalgam hTM).ofA y₀ * g⁻¹) * (g * (puAmalgam hTM).ofA x₀ * g⁻¹) ↔
      (x₀ : G) * y₀ = y₀ * x₀ := by
  constructor
  · intro hc
    have h1 : (puAmalgam hTM).ofA (x₀ * y₀) = (puAmalgam hTM).ofA (y₀ * x₀) := by
      rw [map_mul, map_mul]
      have := congrArg (fun z => g⁻¹ * z * g) hc
      simpa [mul_assoc] using this
    have := congrArg Subtype.val ((puAmalgam hTM).ofA_injective h1)
    simpa using this
  · intro hc
    have h1 : x₀ * y₀ = y₀ * x₀ := Subtype.ext (by simpa using hc)
    calc (g * (puAmalgam hTM).ofA x₀ * g⁻¹) * (g * (puAmalgam hTM).ofA y₀ * g⁻¹)
        = g * (puAmalgam hTM).ofA (x₀ * y₀) * g⁻¹ := by rw [map_mul]; group
      _ = g * (puAmalgam hTM).ofA (y₀ * x₀) * g⁻¹ := by rw [h1]
      _ = _ := by rw [map_mul]; group

omit [Finite G] [Fintype F] in
theorem conj_ofA_conj (hTM : T ≤ M) (g : (puAmalgam hTM).Universal) (x₀ y₀ : ↥M) :
    (g * (puAmalgam hTM).ofA x₀ * g⁻¹) * (g * (puAmalgam hTM).ofA y₀ * g⁻¹) *
        (g * (puAmalgam hTM).ofA x₀ * g⁻¹)⁻¹ =
      g * (puAmalgam hTM).ofA (x₀ * y₀ * x₀⁻¹) * g⁻¹ := by
  rw [map_mul, map_mul, map_inv]
  group

omit [Finite G] [Fintype F] in
theorem conj_ofA_mem_centralizer_iff (hTM : T ≤ M) {K : Subgroup G} (hK : K ≤ M)
    {g : (puAmalgam hTM).Universal} {x₀ : ↥M} :
    g * (puAmalgam hTM).ofA x₀ * g⁻¹ ∈ Subgroup.centralizer
        (((imM hTM K).map (MulAut.conj g).toMonoidHom : Subgroup _) :
          Set (puAmalgam hTM).Universal) ↔
      (x₀ : G) ∈ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc y hy
    exact (conj_ofA_comm_iff hTM (x₀ := ⟨y, hK hy⟩)).1
      (hc _ ((mem_map_conj_imM hTM).2 ⟨⟨y, hK hy⟩, hy, rfl⟩))
  · intro hc z hz
    obtain ⟨y₀, hy₀, rfl⟩ := (mem_map_conj_imM hTM).1 hz
    exact (conj_ofA_comm_iff hTM).2 (hc _ hy₀)

omit [Finite G] [Fintype F] in
theorem stab_conj_eq (hTM : T ≤ M) (g : (puAmalgam hTM).Universal) :
    stab _ (g • baseA (puAmalgam hTM)) = (imM hTM M).map (MulAut.conj g).toMonoidHom := by
  rw [stab_smul, puAmalgam.stab_baseA]

theorem uSub_conj_eq (h : PUHyp M T L) (g : (puAmalgam h.le).Universal) :
    S5.uSub h.le L (g • baseA (puAmalgam h.le)) =
      (imM h.le (Uq M T L)).map (MulAut.conj g).toMonoidHom := by
  rw [S5B.uSub_smul h.le ((Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer),
    S5B.uSub_baseA h]

theorem puTrans_conj_eq (h : PUHyp M T L) (g : (puAmalgam h.le).Universal) :
    puTrans h.le L (g • baseA (puAmalgam h.le)) =
      (imM h.le L).map (MulAut.conj g).toMonoidHom := by
  rw [puTrans_smul h.le ((Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer),
    S5B.puTrans_L_baseA h]

theorem commutator_uSub_conj_eq (h : PUHyp M T L) (g : (puAmalgam h.le).Universal)
    {E₀ : Subgroup G} (hE₀M : E₀ ≤ M) :
    ⁅S5.uSub h.le L (g • baseA (puAmalgam h.le)), (imM h.le E₀).map (MulAut.conj g).toMonoidHom⁆ =
      (imM h.le ⁅Uq M T L, E₀⁆).map (MulAut.conj g).toMonoidHom := by
  rw [uSub_conj_eq h g, ← Subgroup.map_commutator, imM_commutator h.le (Uq_le h.L_le) hE₀M]

omit [Finite G] [Fintype F] in
theorem isPGroup_of_conj (hTM : T ≤ M) (g : (puAmalgam hTM).Universal) {E₀ : Subgroup G}
    (hE₀M : E₀ ≤ M) (hE2 : IsPGroup 2 ((imM hTM E₀).map (MulAut.conj g).toMonoidHom)) :
    IsPGroup 2 E₀ := by
  have e1 : ↥E₀ ≃* ↥(imM hTM E₀) := by
    refine (Subgroup.subgroupOfEquivOfLe hE₀M).symm.trans ?_
    exact Subgroup.equivMapOfInjective _ _ (puAmalgam hTM).ofA_injective
  have e2 : ↥(imM hTM E₀) ≃* ↥((imM hTM E₀).map (MulAut.conj g).toMonoidHom) :=
    Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective
  exact hE2.of_equiv (e1.trans e2).symm

end Transport

section Vertex

theorem mem_centralizer_of_comm (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ stab _ δ)
    (hrel : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L δ) = 2 ^ k)
    {u : (puAmalgam h.le).Universal} (hu : u ∈ ⁅S5.uSub h.le L δ, E⁆)
    (huL : u ∉ Subgroup.centralizer (puTrans h.le L δ : Set (puAmalgam h.le).Universal))
    {m : (puAmalgam h.le).Universal} (hm : m ∈ stab _ δ) (hmu : m * u = u * m) :
    m ∈ Subgroup.centralizer
      ((⁅S5.uSub h.le L δ, E⁆ : Subgroup _) : Set (puAmalgam h.le).Universal) := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hδ
  obtain ⟨E₀, hE₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g hE
  rw [S5B.relIndex_centralizer_smul h g hE₀M] at hrel
  rw [commutator_uSub_conj_eq h g hE₀M] at hu ⊢
  rw [puTrans_conj_eq h g] at huL
  rw [stab_conj_eq h.le g] at hm
  obtain ⟨u₀, hu₀, rfl⟩ := (mem_map_conj_imM h.le).1 hu
  obtain ⟨m₀, -, rfl⟩ := (mem_map_conj_imM h.le).1 hm
  rw [conj_ofA_mem_centralizer_iff h.le (commutator_le_of_le (Uq_le h.L_le) hE₀M)]
  rw [conj_ofA_mem_centralizer_iff h.le h.L_le] at huL
  exact mem_centralizer_of_comm_M h hd hE₀M hrel hu₀ huL m₀.2 ((conj_ofA_comm_iff h.le).1 hmu)

theorem mem_centralizer_of_normalizer (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ stab _ δ)
    (hrel : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L δ) = 2 ^ k)
    {t : (puAmalgam h.le).Universal} (ht : t ∈ stab _ δ) {n : ℕ} (ht2 : t ^ 2 ^ n = 1)
    (htE : ∀ e ∈ E, t * e * t⁻¹ ∈ E) :
    t ∈ Subgroup.centralizer
      ((⁅S5.uSub h.le L δ, E⁆ : Subgroup _) : Set (puAmalgam h.le).Universal) := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hδ
  obtain ⟨E₀, hE₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g hE
  rw [S5B.relIndex_centralizer_smul h g hE₀M] at hrel
  rw [commutator_uSub_conj_eq h g hE₀M]
  rw [stab_conj_eq h.le g] at ht
  obtain ⟨t₀, -, rfl⟩ := (mem_map_conj_imM h.le).1 ht
  rw [conj_ofA_mem_centralizer_iff h.le (commutator_le_of_le (Uq_le h.L_le) hE₀M)]
  refine mem_centralizer_of_normalizer_M h hd hE₀M hrel t₀.2 (n := n) ?_ ?_
  · have h1 : g * (puAmalgam h.le).ofA (t₀ ^ 2 ^ n) * g⁻¹ = 1 := by
      rw [map_pow, ← ht2]
      clear ht2
      induction (2 ^ n) with
      | zero => simp
      | succ m ih => rw [pow_succ, pow_succ, ← ih]; group
    have h2 : (puAmalgam h.le).ofA (t₀ ^ 2 ^ n) = (puAmalgam h.le).ofA 1 := by
      rw [map_one]
      calc (puAmalgam h.le).ofA (t₀ ^ 2 ^ n)
          = g⁻¹ * (g * (puAmalgam h.le).ofA (t₀ ^ 2 ^ n) * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    have := congrArg Subtype.val ((puAmalgam h.le).ofA_injective h2)
    simpa using this
  · intro e he
    have hmem := htE _ ((mem_map_conj_imM h.le).2 ⟨⟨e, hE₀M he⟩, he, rfl⟩)
    rw [conj_ofA_conj] at hmem
    obtain ⟨y₀, hy₀, hye⟩ := (mem_map_conj_imM h.le).1 hmem
    have h3 : (puAmalgam h.le).ofA (t₀ * ⟨e, hE₀M he⟩ * t₀⁻¹) = (puAmalgam h.le).ofA y₀ := by
      have := congrArg (fun z => g⁻¹ * z * g) hye
      simpa [mul_assoc] using this
    have h4 := congrArg Subtype.val ((puAmalgam h.le).ofA_injective h3)
    simp only [MulMemClass.coe_mul, InvMemClass.coe_inv] at h4
    rw [h4]
    exact hy₀

theorem centralizer_sup_eq (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) {u : (puAmalgam h.le).Universal}
    (hu : u ∈ S5.uSub h.le L δ)
    (huL : u ∉ Subgroup.centralizer (puTrans h.le L δ : Set (puAmalgam h.le).Universal))
    {E : Subgroup (puAmalgam h.le).Universal} (hE : E ≤ stab _ δ) (hE2 : IsPGroup 2 E)
    {e : (puAmalgam h.le).Universal} (he : e ∈ E) (heu : e * u ≠ u * e) :
    stab _ δ ⊓ Subgroup.centralizer ({u} : Set (puAmalgam h.le).Universal) ⊔ E = stab _ δ := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hδ
  obtain ⟨E₀, hE₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g hE
  rw [uSub_conj_eq h g] at hu
  rw [puTrans_conj_eq h g] at huL
  obtain ⟨u₀, hu₀, rfl⟩ := (mem_map_conj_imM h.le).1 hu
  obtain ⟨e₀, he₀, rfl⟩ := (mem_map_conj_imM h.le).1 he
  rw [conj_ofA_mem_centralizer_iff h.le h.L_le] at huL
  have hE₀2 := isPGroup_of_conj h.le g hE₀M hE2
  have key := centralizer_sup_eq_M h hd hu₀ huL hE₀M hE₀2 he₀
    (fun hc => heu ((conj_ofA_comm_iff h.le).2 hc))
  refine le_antisymm (sup_le inf_le_left hE) ?_
  have hle : (imM h.le (M ⊓ Subgroup.centralizer ({(u₀ : G)} : Set G))).map
      (MulAut.conj g).toMonoidHom ≤ stab _ (g • baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer ({g * (puAmalgam h.le).ofA u₀ * g⁻¹} :
          Set (puAmalgam h.le).Universal) := by
    intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := (mem_map_conj_imM h.le).1 hx
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    · rw [stab_conj_eq h.le g]
      exact (mem_map_conj_imM h.le).2 ⟨x₀, x₀.2, rfl⟩
    · exact (conj_ofA_comm_iff h.le).2 (Subgroup.mem_centralizer_singleton_iff.1 hx₀.2)
  calc stab _ (g • baseA (puAmalgam h.le)) = (imM h.le M).map (MulAut.conj g).toMonoidHom :=
        stab_conj_eq h.le g
    _ = (imM h.le (M ⊓ Subgroup.centralizer ({(u₀ : G)} : Set G) ⊔ E₀)).map
        (MulAut.conj g).toMonoidHom := by rw [key]
    _ = (imM h.le (M ⊓ Subgroup.centralizer ({(u₀ : G)} : Set G))).map
          (MulAut.conj g).toMonoidHom ⊔ (imM h.le E₀).map (MulAut.conj g).toMonoidHom := by
        rw [S5B.imM_sup_of_le h.le inf_le_left hE₀M, Subgroup.map_sup]
    _ ≤ _ := sup_le_sup_right hle _

theorem exists_conj_not_comm (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) {u : (puAmalgam h.le).Universal}
    (hu : u ∈ S5.uSub h.le L δ)
    (huL : u ∉ Subgroup.centralizer (puTrans h.le L δ : Set (puAmalgam h.le).Universal))
    {E : Subgroup (puAmalgam h.le).Universal} (hE : E ≤ stab _ δ) (hE2 : IsPGroup 2 E)
    (hEQ : ¬ E ≤ Qv _ δ) :
    ∃ m ∈ stab _ δ, ∃ e ∈ E, e * (m * u * m⁻¹) ≠ (m * u * m⁻¹) * e := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hδ
  obtain ⟨E₀, hE₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g hE
  obtain ⟨hE₀2, hE₀O⟩ := S5B.isPGroup_not_le_of_smul h g hE₀M hE2 hEQ
  rw [uSub_conj_eq h g] at hu
  rw [puTrans_conj_eq h g] at huL
  obtain ⟨u₀, hu₀, rfl⟩ := (mem_map_conj_imM h.le).1 hu
  rw [conj_ofA_mem_centralizer_iff h.le h.L_le] at huL
  obtain ⟨m₀, hm₀, e₀, he₀, hne⟩ := exists_conj_not_comm_M h hd hu₀ huL hE₀M hE₀2 hE₀O
  refine ⟨g * (puAmalgam h.le).ofA ⟨m₀, hm₀⟩ * g⁻¹, ?_,
    g * (puAmalgam h.le).ofA ⟨e₀, hE₀M he₀⟩ * g⁻¹,
    (mem_map_conj_imM h.le).2 ⟨⟨e₀, hE₀M he₀⟩, he₀, rfl⟩, fun hc => hne ?_⟩
  · rw [stab_conj_eq h.le g]
    exact (mem_map_conj_imM h.le).2 ⟨⟨m₀, hm₀⟩, hm₀, rfl⟩
  · rw [conj_ofA_conj] at hc
    have := (conj_ofA_comm_iff h.le).1 hc
    simpa using this

theorem card_commutator_le_two (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) (hk : k = 1)
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ stab _ δ)
    (hrel : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L δ) = 2 ^ k) :
    Nat.card ↥⁅S5.uSub h.le L δ, E⁆ ≤ 2 := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hδ
  obtain ⟨E₀, hE₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g hE
  rw [S5B.relIndex_centralizer_smul h g hE₀M] at hrel
  rw [commutator_uSub_conj_eq h g hE₀M, S5B.card_map_conj,
    S5B.card_imM h.le (commutator_le_of_le (Uq_le h.L_le) hE₀M)]
  exact card_commutator_le_two_M h hd hk hE₀M hrel

end Vertex

end S59

end CFSG.Quasithin.MS93
