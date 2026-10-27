module

public import CFSG.Quasithin.Background.ConjTransport
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ModuleSec
public import CFSG.Quasithin.Background.SmithB42HatA6Model
public import CFSG.Quasithin.Background.SmithB42Families
public import CFSG.Quasithin.Background.B4HypCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3D4Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42TypeListAux

public section

namespace CFSG.Quasithin.HatA6

open CFSG.Open CFSG.QuasithinUnique.Setup.X3

variable {V : Type} [CommGroup V]

theorem iInf_fixV_le_fixV_closure {m : ℕ} (A : Fin m → Subgroup (MulAut V)) :
    (⨅ i, fixV (A i)) ≤ fixV (Subgroup.closure (⋃ i, (A i : Set (MulAut V)))) := by
  intro v hv x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
    exact (Subgroup.mem_iInf.1 hv i) y hi
  | one => rfl
  | mul a b _ _ ha hb => rw [MulAut.mul_apply, hb, ha]
  | inv a _ ha =>
    calc a⁻¹ v = a⁻¹ (a v) := by rw [ha]
      _ = v := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]

theorem card_fixV_conj (A : Subgroup (MulAut V)) (l : MulAut V) :
    Nat.card (fixV (A.map (MulAut.conj l).toMonoidHom)) = Nat.card (fixV A) :=
  CFSG.Quasithin.ConjTransport.card_fixV_map_conj A l

theorem card_le_pow_of_le_closure [Finite V] {A L : Subgroup (MulAut V)} (hL : fixV L = ⊥)
    {m : ℕ} (l : Fin m → MulAut V)
    (hle : L ≤ Subgroup.closure (⋃ i, ((A.map (MulAut.conj (l i)).toMonoidHom :
      Subgroup (MulAut V)) : Set (MulAut V)))) :
    Nat.card V ≤ (fixV A).index ^ m := by
  have hbot : (⨅ i, fixV (A.map (MulAut.conj (l i)).toMonoidHom)) = ⊥ := by
    refine eq_bot_iff.2 ((iInf_fixV_le_fixV_closure _).trans ?_)
    rw [← hL]
    intro v hv x hx
    exact hv x (hle hx)
  have h1 := Subgroup.index_iInf_le (fun i => fixV (A.map (MulAut.conj (l i)).toMonoidHom))
  rw [hbot, Subgroup.index_bot] at h1
  have h2 : ∀ i, (fixV (A.map (MulAut.conj (l i)).toMonoidHom)).index = (fixV A).index := by
    intro i
    have e1 := (fixV (A.map (MulAut.conj (l i)).toMonoidHom)).card_mul_index
    have e2 := (fixV A).card_mul_index
    rw [card_fixV_conj] at e1
    have hpos : 0 < Nat.card (fixV A) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (e1.trans e2.symm)
  simp only [h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  exact h1


section B4

variable [Finite V] {G L : Subgroup (MulAut V)}

theorem le_of_b4Hyp_core (hHyp : B4HypCore G L) : L ≤ G := hHyp.1 ▸ quasithinGenFitting_le G

theorem le_normalizer_of_b4Hyp_core (hHyp : B4HypCore G L) :
    G ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
  hHyp.1 ▸ le_normalizer_quasithinGenFitting G

theorem inf_centralizer_le_of_b4Hyp_core (hHyp : B4HypCore G L) :
    G ⊓ Subgroup.centralizer (L : Set (MulAut V)) ≤ L :=
  hHyp.1 ▸ centralizer_quasithinGenFitting_le G

theorem irr_of_b4Hyp_core (hHyp : B4HypCore G L) :
    ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤ :=
  CFSG.QuasithinUnique.Bridge.TypeList.irr_of_isIrrSec hHyp.2.2

theorem fixV_eq_bot_of_b4Hyp_core (hHyp : B4HypCore G L) : fixV L = ⊥ := by
  rcases irr_of_b4Hyp_core hHyp (fixV L) (fun l _ v hv => by rw [hv l ‹_›]; exact hv) with h | h
  · exact h
  · exfalso
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ :=
      CFSG.LocalCores.isQuasisimple_nontrivial (hHyp.2.1)
    have htriv : ∀ x ∈ L, x = 1 := fun x hx => MulEquiv.ext fun v => by
      have : v ∈ fixV L := h ▸ Subgroup.mem_top v
      exact this x hx
    exact hab (Subtype.ext ((htriv a ha).trans (htriv b hb).symm))

theorem le_of_b4Hyp (hHyp : B4Hyp G L) : L ≤ G := le_of_b4Hyp_core hHyp.core

theorem le_normalizer_of_b4Hyp (hHyp : B4Hyp G L) :
    G ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
  le_normalizer_of_b4Hyp_core hHyp.core

theorem inf_centralizer_le_of_b4Hyp (hHyp : B4Hyp G L) :
    G ⊓ Subgroup.centralizer (L : Set (MulAut V)) ≤ L :=
  inf_centralizer_le_of_b4Hyp_core hHyp.core

theorem irr_of_b4Hyp (hHyp : B4Hyp G L) :
    ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤ :=
  irr_of_b4Hyp_core hHyp.core

theorem fixV_eq_bot_of_b4Hyp (hHyp : B4Hyp G L) : fixV L = ⊥ :=
  fixV_eq_bot_of_b4Hyp_core hHyp.core

omit [Finite V] in
theorem eq_one_of_mem_center (hZ : Nat.card (Subgroup.center ↥L) = 3) {a : MulAut V}
    (ha : a ∈ L) (hac : ⟨a, ha⟩ ∈ Subgroup.center ↥L) (ha2 : a ^ 2 = 1) : a = 1 := by
  have h1 : orderOf (⟨⟨a, ha⟩, hac⟩ : ↥(Subgroup.center ↥L)) ∣ 3 := by
    rw [← hZ]
    exact orderOf_dvd_natCard _
  have h2 : orderOf (⟨⟨a, ha⟩, hac⟩ : ↥(Subgroup.center ↥L)) ∣ 2 := by
    refine orderOf_dvd_of_pow_eq_one ?_
    apply Subtype.ext
    apply Subtype.ext
    exact ha2
  have h3 : orderOf (⟨⟨a, ha⟩, hac⟩ : ↥(Subgroup.center ↥L)) = 1 :=
    Nat.eq_one_of_dvd_coprimes (by norm_num) h1 h2
  rw [orderOf_eq_one_iff] at h3
  exact congrArg (fun x : ↥(Subgroup.center ↥L) => ((x : ↥L) : MulAut V)) h3

omit [Finite V] in
private theorem short_generation_ker {G L : Subgroup (MulAut V)}
    [hLn : (L.subgroupOf G).Normal]
    (hLG : L ≤ G)
    (hCL : G ⊓ Subgroup.centralizer (L : Set (MulAut V)) ≤ L)
    (hq : CFSG.IsQuasisimple ↥L)
    (eL : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 6)) :
    ∃ eQ : (↥(L.subgroupOf G) ⧸ Subgroup.center ↥(L.subgroupOf G)) ≃*
        alternatingGroup (Fin 6),
      (∀ h : ↥G, outAct (L.subgroupOf G) eQ h = 1 →
        h ∈ (Subgroup.center ↥(L.subgroupOf G)).map (L.subgroupOf G).subtype) ∧
      (∀ h : ↥G, h ∈ Subgroup.centralizer (L.subgroupOf G : Set ↥G) →
        (h : MulAut V) ∈ L ∧ ∀ l ∈ L, l * (h : MulAut V) = (h : MulAut V) * l) := by
  classical
  set L' : Subgroup ↥G := L.subgroupOf G with hL'
  have : L'.Normal := by rw [hL']; exact hLn
  let eLL : ↥L' ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLG
  have hq' : CFSG.IsQuasisimple ↥L' := CFSG.LocalCores.isQuasisimple_of_mulEquiv eLL.symm hq
  have : Group.IsPerfect ↥L' := hq'.1
  let eQ : ↥L' ⧸ Subgroup.center ↥L' ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.congr _ _ eLL (Subgroup.map_center_eq eLL)).trans eL
  have hcen : ∀ h : ↥G, h ∈ Subgroup.centralizer (L' : Set ↥G) →
      (h : MulAut V) ∈ L ∧ ∀ l ∈ L, l * (h : MulAut V) = (h : MulAut V) * l := by
    intro h hc
    have hcV : ∀ l ∈ L, l * (h : MulAut V) = (h : MulAut V) * l := by
      intro l hl
      have := Subgroup.mem_centralizer_iff.1 hc ⟨l, hLG hl⟩ (by exact hl)
      exact congrArg Subtype.val this
    refine ⟨hCL ⟨h.2, Subgroup.mem_centralizer_iff.2 fun l hl => hcV l hl⟩, hcV⟩
  have hker : ∀ h : ↥G, outAct L' eQ h = 1 → h ∈ (Subgroup.center ↥L').map L'.subtype := by
    intro h hh
    obtain ⟨hhL, hcV⟩ := hcen h (mem_centralizer_of_outAct_eq_one L' eQ hh)
    have hhL' : h ∈ L' := by rw [hL']; exact Subgroup.mem_subgroupOf.2 hhL
    refine ⟨⟨h, hhL'⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact hcV _ y.2
  exact ⟨eQ, hker, hcen⟩

omit [Finite V] in
private theorem short_generation_image {G L : Subgroup (MulAut V)}
    [hLn : (L.subgroupOf G).Normal] [hperf : Group.IsPerfect ↥(L.subgroupOf G)]
    (hZ3 : Nat.card (Subgroup.center ↥L) = 3)
    (eQ : (↥(L.subgroupOf G) ⧸ Subgroup.center ↥(L.subgroupOf G)) ≃* alternatingGroup (Fin 6))
    (hcen : ∀ h : ↥G, h ∈ Subgroup.centralizer (L.subgroupOf G : Set ↥G) →
      (h : MulAut V) ∈ L ∧ ∀ l ∈ L, l * (h : MulAut V) = (h : MulAut V) * l)
    {A : Subgroup (MulAut V)} (hAG : A ≤ G) (hA1 : A ≠ ⊥) (hAe : IsElemAbelian2 A) :
    Nat.card ↥((A.subgroupOf G).map (outAct (L.subgroupOf G) eQ)) = Nat.card ↥A ∧
      CFSG.IsElementaryAbelian 2
        ↥((A.subgroupOf G).map (outAct (L.subgroupOf G) eQ)) := by
  classical
  have hinjA : ∀ a ∈ A.subgroupOf G, outAct (L.subgroupOf G) eQ a = 1 → a = 1 := by
    intro a ha hh
    obtain ⟨hhL, hcV⟩ := hcen a (mem_centralizer_of_outAct_eq_one (L.subgroupOf G) eQ hh)
    have hac : (⟨(a : MulAut V), hhL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hcV _ y.2)
    exact Subtype.ext (eq_one_of_mem_center hZ3 hhL hac (hAe.2 _ ha))
  have hinj : Function.Injective
      ((outAct (L.subgroupOf G) eQ).comp (A.subgroupOf G).subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    exact Subtype.ext (hinjA a.1 a.2 ha)
  have hcardA : Nat.card ↥((A.subgroupOf G).map (outAct (L.subgroupOf G) eQ)) =
      Nat.card ↥A := by
    have h1 : ((outAct (L.subgroupOf G) eQ).comp (A.subgroupOf G).subtype).range =
        (A.subgroupOf G).map (outAct (L.subgroupOf G) eQ) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← h1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAG).toEquiv
  have hAbar_ne : (A.subgroupOf G).map (outAct (L.subgroupOf G) eQ) ≠ ⊥ := by
    intro hbot
    apply hA1
    rw [eq_bot_iff]
    intro a ha
    have h1 : outAct (L.subgroupOf G) eQ ⟨a, hAG ha⟩ ∈
        (A.subgroupOf G).map (outAct (L.subgroupOf G) eQ) := ⟨⟨a, hAG ha⟩, ha, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 := hinjA ⟨a, hAG ha⟩ ha h1
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val h2
  have hAel : CFSG.IsElementaryAbelian 2 ↥A :=
    B1.isElementaryAbelian_of_isElemAbelian2 hAe
  have : CFSG.IsElementaryAbelian 2 ↥(A.subgroupOf G) :=
    CFSG.IsElementaryAbelian.subgroupOf hAG
  exact ⟨hcardA, CFSG.IsElementaryAbelian.map (outAct (L.subgroupOf G) eQ)⟩

omit [Finite V] in
private theorem short_generation_of_kernel {G L : Subgroup (MulAut V)}
    [hLn : (L.subgroupOf G).Normal] [hperf : Group.IsPerfect ↥(L.subgroupOf G)]
    (hLG : L ≤ G)
    (eQ : (↥(L.subgroupOf G) ⧸ Subgroup.center ↥(L.subgroupOf G)) ≃* alternatingGroup (Fin 6))
    (hker : ∀ h : ↥G, outAct (L.subgroupOf G) eQ h = 1 →
      h ∈ (Subgroup.center ↥(L.subgroupOf G)).map (L.subgroupOf G).subtype)
    {A : Subgroup (MulAut V)} (hA1 : A ≠ ⊥)
    (hcardA : Nat.card ↥((A.subgroupOf G).map (outAct (L.subgroupOf G) eQ)) = Nat.card ↥A)
    (himgel : CFSG.IsElementaryAbelian 2
      ↥((A.subgroupOf G).map (outAct (L.subgroupOf G) eQ))) :
    ∃ r m : ℕ, Nat.card A = 2 ^ r ∧ 1 ≤ r ∧ r ≤ 3 ∧ m * r ≤ 6 ∧
      ∃ l : Fin m → MulAut V, (∀ i, l i ∈ L) ∧
        L ≤ Subgroup.closure (⋃ i, ((A.map (MulAut.conj (l i)).toMonoidHom :
          Subgroup (MulAut V)) : Set (MulAut V))) := by
  classical
  have hAbar_ne : (A.subgroupOf G).map (outAct (L.subgroupOf G) eQ) ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥((A.subgroupOf G).map (outAct (L.subgroupOf G) eQ)) = 1 := by
      rw [hbot, Subgroup.card_bot]
    rw [hcardA] at h1
    exact hA1 (Subgroup.card_eq_one.1 h1)
  have : CFSG.IsElementaryAbelian 2
      ↥((A.subgroupOf G).map (outAct (L.subgroupOf G) eQ)) := himgel
  obtain ⟨r, m, hr, hr1, hr3, hmr, s, hgen⟩ :=
    CFSG.QuasithinUnique.Setup.X3Aut.a6ShortGeneration.2.2.2 _ hAbar_ne inferInstance
  obtain ⟨l, hl⟩ := L_le_closure_of_inner_generation (L.subgroupOf G) eQ hker
    (A.subgroupOf G) s hgen
  refine ⟨r, m, hcardA ▸ hr, hr1, hr3, hmr, fun i => ((l i : ↥G) : MulAut V),
    fun i => (l i).2, ?_⟩
  intro x hx
  have hx' : (⟨x, hLG hx⟩ : ↥G) ∈ L.subgroupOf G := hx
  have h1 := Subgroup.mem_map_of_mem G.subtype (hl hx')
  rw [MonoidHom.map_closure] at h1
  refine Subgroup.closure_mono ?_ h1
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
  obtain ⟨a, ha, rfl⟩ := hi
  refine Set.mem_iUnion.2 ⟨i, ⟨(a : MulAut V), ha, rfl⟩⟩

theorem short_generation_core (hHyp : B4HypCore G L) (hP : B42TypeHatA6 ↥L)
    {A : Subgroup (MulAut V)} (hAG : A ≤ G) (hA1 : A ≠ ⊥) (hAe : IsElemAbelian2 A) :
    ∃ r m : ℕ, Nat.card A = 2 ^ r ∧ 1 ≤ r ∧ r ≤ 3 ∧ m * r ≤ 6 ∧
      ∃ l : Fin m → MulAut V, (∀ i, l i ∈ L) ∧
        L ≤ Subgroup.closure (⋃ i, ((A.map (MulAut.conj (l i)).toMonoidHom :
          Subgroup (MulAut V)) : Set (MulAut V))) := by
  obtain ⟨hq, hZ3, ⟨eL⟩⟩ := hP
  have hLG := le_of_b4Hyp_core hHyp
  have hGN := le_normalizer_of_b4Hyp_core hHyp
  have hCL := inf_centralizer_le_of_b4Hyp_core hHyp
  have : (L.subgroupOf G).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLG).2 hGN
  have : Group.IsPerfect ↥(L.subgroupOf G) := by
    have hqs := CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hLG).symm hq
    exact hqs.1
  obtain ⟨eQ, hker, hcen⟩ := short_generation_ker hLG hCL hq eL
  obtain ⟨hcardA, himgel⟩ := short_generation_image hZ3 eQ hcen hAG hA1 hAe
  exact short_generation_of_kernel hLG eQ hker hA1 hcardA himgel

theorem short_generation (hHyp : B4Hyp G L) (hP : B42TypeHatA6 ↥L) {A : Subgroup (MulAut V)}
    (hAG : A ≤ G) (hA1 : A ≠ ⊥) (hAe : IsElemAbelian2 A) :
    ∃ r m : ℕ, Nat.card A = 2 ^ r ∧ 1 ≤ r ∧ r ≤ 3 ∧ m * r ≤ 6 ∧
      ∃ l : Fin m → MulAut V, (∀ i, l i ∈ L) ∧
        L ≤ Subgroup.closure (⋃ i, ((A.map (MulAut.conj (l i)).toMonoidHom :
          Subgroup (MulAut V)) : Set (MulAut V))) :=
  short_generation_core hHyp.core hP hAG hA1 hAe

end B4


theorem mem_fixV_zpowers_iff {a : MulAut V} {v : V} :
    v ∈ fixV (Subgroup.zpowers a) ↔ a v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

section Card

variable [Finite V]

theorem exists_gen_small (hsq2 : ∀ v : V, v ^ 2 = 1) {z : MulAut V} (h3 : z ^ 3 = 1)
    (hfp : ∀ v, z v = v → v = 1) (hV : Nat.card V = 4 ∨ Nat.card V = 16) :
    ∃ w₁ w₂ : V, Subgroup.closure ({w₁, z w₁, w₂, z w₂} : Set V) = ⊤ := by
  have hd16 : Nat.card V ∣ 16 := by
    rcases hV with h | h
    · rw [h]; norm_num
    · rw [h]
  have hcl : ∀ S : Set V, (∀ s ∈ S, z s ∈ Subgroup.closure S) →
      Nat.card (Subgroup.closure S) ∣ 16 ∧ Nat.card (Subgroup.closure S) % 3 = 1 :=
    fun S hzS => ⟨(Subgroup.card_subgroup_dvd_card _).trans hd16,
      H13.card_mod_three_of_sub h3 (H13.mem_closure_of_map_gen hzS) fun s _ hs => hfp s hs⟩
  have hcases : ∀ c : ℕ, c ∣ 16 → c % 3 = 1 → c = 1 ∨ c = 4 ∨ c = 16 := by
    intro c hc h3c
    rcases H13.card_cases_of_dvd (hc.trans (by norm_num : 16 ∣ 64)) h3c with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · rw [h] at hc; norm_num at hc
  have hzz : ∀ w : V, z (z w) = w * z w := fun w =>
    H13.zz_eq_of_fpf hsq2 h3 (W := ⊤) (fun _ _ => trivial) (fun w _ hw => hfp w hw) trivial
  have hnt : Nontrivial V := by
    have h1 : 1 < Nat.card V := by rcases hV with h | h <;> omega
    exact Finite.one_lt_card_iff_nontrivial.1 h1
  obtain ⟨w₁, hw₁⟩ := exists_ne (1 : V)
  set S₁ := Subgroup.closure ({w₁, z w₁} : Set V) with hS₁
  have hzS₁ : ∀ s ∈ ({w₁, z w₁} : Set V), z s ∈ S₁ := by
    rintro _ (rfl | rfl)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    · rw [hzz]
      exact S₁.mul_mem (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  obtain ⟨hS₁d, hS₁m⟩ : Nat.card S₁ ∣ 16 ∧ Nat.card S₁ % 3 = 1 := hcl _ hzS₁
  have hw₁S : w₁ ∈ S₁ := Subgroup.subset_closure (Set.mem_insert _ _)
  have hS₁1 : Nat.card S₁ ≠ 1 := fun h => hw₁ (by
    rw [Subgroup.card_eq_one] at h; rw [h] at hw₁S; exact hw₁S)
  by_cases hS₁top : S₁ = ⊤
  · refine ⟨w₁, w₁, ?_⟩
    rw [← hS₁top, hS₁]
    congr 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hS₁4 : Nat.card S₁ = 4 := by
    have hlt : Nat.card S₁ < Nat.card V := by
      rw [← Subgroup.card_top (G := V)]
      exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.2 hS₁top)
    rcases hcases _ hS₁d hS₁m with h | h | h
    · exact absurd h hS₁1
    · exact h
    · rcases hV with hV | hV <;> omega
  obtain ⟨w₂, hw₂⟩ : ∃ w₂ : V, w₂ ∉ S₁ := by
    by_contra hcon
    push Not at hcon
    exact hS₁top (eq_top_iff.2 fun x _ => hcon x)
  set S₂ := Subgroup.closure ({w₁, z w₁, w₂, z w₂} : Set V) with hS₂
  have hmem : ∀ x ∈ ({w₁, z w₁, w₂, z w₂} : Set V), x ∈ S₂ := fun x hx =>
    Subgroup.subset_closure hx
  have hzS₂ : ∀ s ∈ ({w₁, z w₁, w₂, z w₂} : Set V), z s ∈ S₂ := by
    rintro _ (rfl | rfl | rfl | rfl)
    · exact hmem _ (by simp)
    · rw [hzz]
      exact S₂.mul_mem (hmem _ (by simp)) (hmem _ (by simp))
    · exact hmem _ (by simp)
    · rw [hzz]
      exact S₂.mul_mem (hmem _ (by simp)) (hmem _ (by simp))
  obtain ⟨hS₂d, hS₂m⟩ : Nat.card S₂ ∣ 16 ∧ Nat.card S₂ % 3 = 1 := hcl _ hzS₂
  have hS₁S₂ : S₁ < S₂ := by
    refine lt_of_le_of_ne (Subgroup.closure_mono (by
      rintro _ (rfl | rfl)
      · simp
      · simp)) fun h => hw₂ (h ▸ hmem _ (by simp))
  have hcard := Subgroup.card_lt_of_lt hS₁S₂
  rw [hS₁4] at hcard
  have hle : Nat.card S₂ ≤ Nat.card V := Subgroup.card_le_card_group S₂
  have hS₂top : Nat.card S₂ = Nat.card V := by
    rcases hcases _ hS₂d hS₂m with h | h | h <;> rcases hV with hV | hV <;> omega
  exact ⟨w₁, w₂, Subgroup.eq_top_of_card_eq S₂ hS₂top⟩

theorem card_centralizer_le_sq {z : MulAut V} {w₁ w₂ : V}
    (hgen : Subgroup.closure ({w₁, z w₁, w₂, z w₂} : Set V) = ⊤) :
    Nat.card (Subgroup.centralizer ({z} : Set (MulAut V))) ≤ Nat.card V ^ 2 := by
  let f : ↥(Subgroup.centralizer ({z} : Set (MulAut V))) → V × V :=
    fun g => ((g : MulAut V) w₁, (g : MulAut V) w₂)
  have hc : ∀ (k : ↥(Subgroup.centralizer ({z} : Set (MulAut V)))) (x : V),
      (k : MulAut V) (z x) = z ((k : MulAut V) x) := fun k x =>
    congrArg (fun F : MulAut V => F x) (Subgroup.mem_centralizer_singleton_iff.mp k.2)
  have hinj : Function.Injective f := by
    intro g g' h
    have h1 : (g : MulAut V) w₁ = (g' : MulAut V) w₁ := congrArg Prod.fst h
    have h2 : (g : MulAut V) w₂ = (g' : MulAut V) w₂ := congrArg Prod.snd h
    let E := (g : MulAut V).toMonoidHom.eqLocus (g' : MulAut V).toMonoidHom
    have hE : ⊤ ≤ E := by
      rw [← hgen, Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact h1
      · show (g : MulAut V) (z w₁) = (g' : MulAut V) (z w₁)
        rw [hc g, hc g', h1]
      · exact h2
      · show (g : MulAut V) (z w₂) = (g' : MulAut V) (z w₂)
        rw [hc g, hc g', h2]
    exact Subtype.ext (MulEquiv.ext fun x => hE (Subgroup.mem_top x))
  calc Nat.card _ ≤ Nat.card (V × V) := Nat.card_le_card_of_injective f hinj
    _ = Nat.card V ^ 2 := by rw [Nat.card_prod, pow_two]

variable {G L : Subgroup (MulAut V)}

theorem exists_center_gen_core (hHyp : B4HypCore G L) (hP : B42TypeHatA6 ↥L) :
    ∃ z : ↥L, Subgroup.center ↥L = Subgroup.zpowers z ∧ (z : MulAut V) ^ 3 = 1 ∧
      (z : MulAut V) ≠ 1 ∧ ∀ v : V, (z : MulAut V) v = v → v = 1 := by
  obtain ⟨-, hZ, -⟩ := hP
  have hZ1 : Subgroup.center ↥L ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZ
    omega
  obtain ⟨⟨z, hzc⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZ1
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have h3 : z ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥(Subgroup.center ↥L)) (x := ⟨z, hzc⟩)
    rw [hZ] at h
    exact congrArg Subtype.val h
  have hzV : (z : MulAut V) ≠ 1 := fun h => hz1' (Subtype.ext h)
  refine ⟨z, ?_, by rw [← Subgroup.coe_pow, h3]; rfl, hzV, ?_⟩
  · have hle : Subgroup.zpowers z ≤ Subgroup.center ↥L := Subgroup.zpowers_le.2 hzc
    have hord : orderOf z = 3 := orderOf_eq_prime h3 hz1'
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hZ, Nat.card_zpowers, hord]
  ·
    have hinv : ∀ l ∈ L, ∀ v ∈ fixV (Subgroup.zpowers (z : MulAut V)), l v ∈
        fixV (Subgroup.zpowers (z : MulAut V)) := by
      intro l hl v hv x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      have hcomm : (z : MulAut V) ^ k * l = l * (z : MulAut V) ^ k := by
        have h1 := Subgroup.mem_center_iff.1 hzc ⟨l, hl⟩
        have h2 : (z : MulAut V) * l = l * (z : MulAut V) := (congrArg Subtype.val h1).symm
        exact (Commute.zpow_left h2 k)
      calc ((z : MulAut V) ^ k) (l v) = ((z : MulAut V) ^ k * l) v := rfl
        _ = (l * (z : MulAut V) ^ k) v := by rw [hcomm]
        _ = l v := by
          change l (((z : MulAut V) ^ k) v) = l v
          rw [hv _ (Subgroup.zpow_mem_zpowers _ k)]
    rcases irr_of_b4Hyp_core hHyp _ hinv with h | h
    · intro v hv
      have : v ∈ fixV (Subgroup.zpowers (z : MulAut V)) := (mem_fixV_zpowers_iff).2 hv
      rw [h, Subgroup.mem_bot] at this
      exact this
    · exfalso
      apply hzV
      refine MulEquiv.ext fun v => ?_
      have : v ∈ fixV (Subgroup.zpowers (z : MulAut V)) := h ▸ Subgroup.mem_top v
      exact this _ (Subgroup.mem_zpowers _)

theorem exists_center_gen (hHyp : B4Hyp G L) (hP : B42TypeHatA6 ↥L) :
    ∃ z : ↥L, Subgroup.center ↥L = Subgroup.zpowers z ∧ (z : MulAut V) ^ 3 = 1 ∧
      (z : MulAut V) ≠ 1 ∧ ∀ v : V, (z : MulAut V) v = v → v = 1 :=
  exists_center_gen_core hHyp.core hP


theorem index_le_of_offender {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A) :
    (fixV A).index ≤ Nat.card A :=
  CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.index_fixV_le_card hA

theorem card_V_core (hV : ∀ v : V, v ^ 2 = 1) (hHyp : B4HypCore G L) (hP : B42TypeHatA6 ↥L)
    {A : Subgroup (MulAut V)} (hA : IsFFStarOffender G A) : Nat.card V = 2 ^ 6 := by
  obtain ⟨r, m, hr, -, -, hmr, l, -, hle⟩ := short_generation_core hHyp hP hA.1 hA.2.1 hA.2.2.1
  have h1 := card_le_pow_of_le_closure (fixV_eq_bot_of_b4Hyp_core hHyp) l hle
  have hup : Nat.card V ≤ 2 ^ 6 := by
    refine h1.trans ((Nat.pow_le_pow_left (index_le_of_offender hA) m).trans ?_)
    rw [hr, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by rw [mul_comm]; exact hmr)
  obtain ⟨z, hzcen, h3, hz1, hfp⟩ := exists_center_gen_core hHyp hP
  have hzc : z ∈ Subgroup.center ↥L := hzcen ▸ Subgroup.mem_zpowers z
  have hmod : Nat.card V % 3 = 1 := H13.card_mod_three_of_fpf (z : MulAut V) h3 hfp
  obtain ⟨k, hk⟩ : ∃ k, Nat.card V = 2 ^ k :=
    (IsPGroup.iff_card).1 (isPGroup_two_of_sq_eq_one hV)
  have hk6 : k ≤ 6 := by
    rw [hk] at hup
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hup
  obtain ⟨hq, hZ, ⟨e⟩⟩ := hP
  have hL : Nat.card L = 1080 := (quasisimple_card hq.1 hZ e).2
  have hLC : L ≤ Subgroup.centralizer ({(z : MulAut V)} : Set (MulAut V)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := (Subgroup.mem_center_iff.1 hzc) ⟨x, hx⟩
    exact congrArg Subtype.val this
  interval_cases k
  · exfalso
    have : Subsingleton V := (Nat.card_eq_one_iff_unique.1 (by rw [hk]; rfl)).1
    exact hz1 (MulEquiv.ext fun v => Subsingleton.elim _ _)
  · rw [hk] at hmod; norm_num at hmod
  · obtain ⟨w₁, w₂, hgen⟩ := exists_gen_small (fun v => hV v) h3 hfp (Or.inl (by rw [hk]; rfl))
    have := (Subgroup.card_le_of_le hLC).trans (card_centralizer_le_sq hgen)
    rw [hL, hk] at this
    norm_num at this
  · rw [hk] at hmod; norm_num at hmod
  · obtain ⟨w₁, w₂, hgen⟩ := exists_gen_small (fun v => hV v) h3 hfp (Or.inr (by rw [hk]; rfl))
    have := (Subgroup.card_le_of_le hLC).trans (card_centralizer_le_sq hgen)
    rw [hL, hk] at this
    norm_num at this
  · rw [hk] at hmod; norm_num at hmod
  · exact hk

theorem card_V (hV : ∀ v : V, v ^ 2 = 1) (hHyp : B4Hyp G L) (hP : B42TypeHatA6 ↥L)
    {A : Subgroup (MulAut V)} (hA : IsFFStarOffender G A) : Nat.card V = 2 ^ 6 :=
  card_V_core hV hHyp.core hP hA

end Card

end CFSG.Quasithin.HatA6
