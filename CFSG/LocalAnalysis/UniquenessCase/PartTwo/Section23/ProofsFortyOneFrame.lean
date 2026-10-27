module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsThirtyNineAbFinal
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20g
public import CFSG.LinearAlgebra.SL2LineStabilizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup Matrix
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

private theorem card_le_card_of_forall_eq_smul {K X : Type*} [Field K] [Finite K]
    (β : X → Multiplicative (Fin 2 → K)) (hβ : Function.Injective β) {e : Fin 2 → K}
    (he : e ≠ 0) (hfix : ∀ v : X, ∃ c : K, β v = Multiplicative.ofAdd (c • e)) :
    Nat.card X ≤ Nat.card K := by
  classical
  let f : X → K := fun v => Classical.choose (hfix v)
  have hf : ∀ v : X, β v = Multiplicative.ofAdd (f v • e) := fun v =>
    Classical.choose_spec (hfix v)
  have hinj : Function.Injective f := by
    intro v w h
    apply hβ
    rw [hf v, hf w, h]
  exact Nat.card_le_card_of_injective f hinj

private theorem relIndex_inf_le_relIndex_inf_of_le {G : Type*} [Group G] [Finite G]
    {A B K : Subgroup G} (hAB : A ≤ B) :
    (A ⊓ K).relIndex A ≤ (B ⊓ K).relIndex B := by
  have hKpos : K.relIndex B ≠ 0 := by
    have hdvd := Subgroup.relIndex_dvd_card (H := K) (K := B)
    exact (Nat.pos_of_dvd_of_pos hdvd Nat.card_pos).ne'
  calc (A ⊓ K).relIndex A ≤ K.relIndex A := by
        have h := Subgroup.relIndex_inf_le (H := A) (K := K) (L := A)
        rwa [Subgroup.relIndex_self, one_mul] at h
    _ ≤ K.relIndex B := Subgroup.relIndex_le_of_le_right hAB hKpos
    _ = (K ⊓ B).relIndex B := (Subgroup.inf_relIndex_right K B).symm
    _ = (B ⊓ K).relIndex B := by rw [inf_comm]

private theorem alpha_ne_one_of_not_mem_centralizer {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} {hV : IsElemAbelian 2 c.V}
    {hLV : c.L ≤ Subgroup.normalizer (c.V : Set G)}
    {κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV
      (CFSG.Open.pRank 2 D.Z)}
    {t l : G}
    (hker : κ.α.ker = (c.L ⊓ Subgroup.centralizer (c.V : Set G)).subgroupOf c.L)
    (htC : t ∉ Subgroup.centralizer (c.V : Set G))
    (hl : l ∈ D.T ⊓ c.L)
    (hw : t * l⁻¹ ∈ Subgroup.centralizer (c.V : Set G)) :
    κ.α ⟨l, (Subgroup.mem_inf.mp hl).2⟩ ≠ 1 := by
  intro h1
  have hmem : ⟨l, (Subgroup.mem_inf.mp hl).2⟩ ∈ κ.α.ker := MonoidHom.mem_ker.mpr h1
  rw [hker, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hmem
  apply htC
  have ht_eq : t = (t * l⁻¹) * l := by group
  rw [ht_eq]
  exact (Subgroup.centralizer (c.V : Set G)).mul_mem hw hmem.2

private theorem exists_eigenvector {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    {hV : IsElemAbelian 2 c.V}
    {hLV : c.L ≤ Subgroup.normalizer (c.V : Set G)}
    {κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV
      (CFSG.Open.pRank 2 D.Z)}
    {l : G} (hlT : l ∈ D.T) (hlL : l ∈ c.L) :
    ∃ e : Fin 2 → κ.K, e ≠ 0 ∧
      (κ.α ⟨l, hlL⟩ : Matrix (Fin 2) (Fin 2) κ.K) *ᵥ e = e := by
  classical
  obtain ⟨z₀, hz₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (uc22main1_Z_ne_bot D)
  have hz₀V : (z₀ : G) ∈ c.V := uc22p22v_le_conjClosure c.N D.Z z₀.2
  let zV : ↥c.V := ⟨z₀, hz₀V⟩
  let e : Fin 2 → κ.K := Multiplicative.toAdd (κ.β zV)
  have he : e ≠ 0 := by
    intro h0
    have h1 : κ.β zV = 1 := Multiplicative.toAdd.injective (by simpa [e] using h0)
    have h2 : zV = 1 := κ.β_bij.1 (by simpa using h1)
    exact hz₀1 (Subtype.ext (by simpa [zV] using congrArg Subtype.val h2))
  have hefix : (κ.α ⟨l, hlL⟩ : Matrix (Fin 2) (Fin 2) κ.K) *ᵥ e = e := by
    have hcomm : Commute l (z₀ : G) := by
      rw [Commute]
      exact (Subgroup.mem_centralizer_iff.mp
        (uc22main1_T_le_centralizer D hlT) (z₀ : G) z₀.2).symm
    have hconj : CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjV hLV ⟨l, hlL⟩ zV = zV := by
      apply Subtype.ext
      calc l * (z₀ : G) * l⁻¹ = (z₀ : G) * l * l⁻¹ := by rw [hcomm]
        _ = z₀ := by group
    have h := congrArg Multiplicative.toAdd (κ.β_act ⟨l, hlL⟩ zV)
    rw [hconj] at h
    simpa [e] using h.symm
  exact ⟨e, he, hefix⟩

private theorem exists_smul_of_mem_inf_centralizer {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} {hV : IsElemAbelian 2 c.V} {hLV : c.L ≤ Subgroup.normalizer c.V}
    {κ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Coordinates c.L c.V hV hLV
      (CFSG.Open.pRank 2 D.Z)}
    {t l : G} (hlT : l ∈ D.T) (hlL : l ∈ c.L)
    (hw : t * l⁻¹ ∈ Subgroup.centralizer (c.V : Set G)) (hαl_ne : κ.α ⟨l, hlL⟩ ≠ 1)
    {e : Fin 2 → κ.K} (he : e ≠ 0)
    (hefix : (κ.α ⟨l, hlL⟩ : Matrix (Fin 2) (Fin 2) κ.K) *ᵥ e = e)
    (v : ↥(c.V ⊓ Subgroup.centralizer ({t} : Set G))) :
    ∃ s : κ.K, κ.β ⟨(v : G), v.2.1⟩ = Multiplicative.ofAdd (s • e) := by
  have hvt : t * (v : G) * t⁻¹ = (v : G) := by
    have hcomm : (v : G) * t = t * (v : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp v.2.2
    calc t * (v : G) * t⁻¹ = (v : G) * t * t⁻¹ := by rw [← hcomm]
      _ = v := by group
  have hmemV : l * (v : G) * l⁻¹ ∈ c.V :=
    (Subgroup.mem_normalizer_iff.mp (hLV hlL) (v : G)).mp v.2.1
  have hcommCentral : Commute (t * l⁻¹) (l * (v : G) * l⁻¹) :=
    (Subgroup.mem_centralizer_iff.mp hw _ hmemV).symm
  have heq : t * (v : G) * t⁻¹ = l * (v : G) * l⁻¹ := by
    calc t * (v : G) * t⁻¹ =
        (t * l⁻¹) * (l * (v : G) * l⁻¹) * (t * l⁻¹)⁻¹ := by group
      _ = l * (v : G) * l⁻¹ := by rw [hcommCentral]; group
  have hvl : l * (v : G) * l⁻¹ = (v : G) := by rw [← heq, hvt]
  have hconjV : CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjV hLV ⟨l, hlL⟩
      ⟨(v : G), v.2.1⟩ = ⟨(v : G), v.2.1⟩ := Subtype.ext hvl
  have hfixα : (κ.α ⟨l, hlL⟩ : Matrix (Fin 2) (Fin 2) κ.K) *ᵥ
      Multiplicative.toAdd (κ.β ⟨(v : G), v.2.1⟩) =
      Multiplicative.toAdd (κ.β ⟨(v : G), v.2.1⟩) := by
    have h := congrArg Multiplicative.toAdd (κ.β_act ⟨l, hlL⟩ ⟨(v : G), v.2.1⟩)
    rw [hconjV] at h
    exact h.symm
  obtain ⟨s, hs⟩ := CFSG.LinearAlgebra.exists_eq_smul_of_mulVec_eq_self (κ.α ⟨l, hlL⟩)
    hαl_ne he hefix hfixα
  exact ⟨s, by rw [← hs]; rfl⟩

private theorem card_inf_centralizer_le_of_not_mem (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {t : G} (ht : t ∈ D.T)
    (htC : t ∉ Subgroup.centralizer (c.V : Set G)) :
    Nat.card ↥(c.V ⊓ Subgroup.centralizer ({t} : Set G)) ≤
      2 ^ CFSG.Open.pRank 2 D.Z := by
  classical
  obtain ⟨hV, hLV, κ, hker, hcardK⟩ := c.exists_coordinates_V D Ch h4 h23 h1930
  obtain ⟨l, hl, hw⟩ :=
    exists_mem_T_inf_L_mul_inv_mem_centralizer D Ch h4 h23 h1930 c ht
  have hlT : l ∈ D.T := (Subgroup.mem_inf.mp hl).1
  have hlL : l ∈ c.L := (Subgroup.mem_inf.mp hl).2
  have hαl_ne := alpha_ne_one_of_not_mem_centralizer (c := c) (hV := hV) (hLV := hLV)
    (κ := κ) hker htC hl hw
  obtain ⟨e, he, hefix⟩ := exists_eigenvector (c := c) (hV := hV) (hLV := hLV)
    (κ := κ) hlT hlL
  have hβ : Function.Injective
      (fun v : ↥(c.V ⊓ Subgroup.centralizer ({t} : Set G)) =>
        κ.β ⟨(v : G), v.2.1⟩) := by
    intro v w h
    have hvV : (⟨(v : G), v.2.1⟩ : ↥c.V) = ⟨(w : G), w.2.1⟩ := κ.β_bij.1 h
    exact Subtype.ext (congrArg (fun x : ↥c.V => (x : G)) hvV)
  have hcard := card_le_card_of_forall_eq_smul _ hβ he (fun v =>
    exists_smul_of_mem_inf_centralizer (c := c) (hV := hV) (hLV := hLV) (κ := κ)
      hlT hlL hw hαl_ne he hefix v)
  rwa [hcardK] at hcard

private theorem inf_centralizer_eq_Z_of_mem_T (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {t : G} (ht : t ∈ D.T)
    (htC : t ∉ Subgroup.centralizer (c.V : Set G)) :
    c.V ⊓ Subgroup.centralizer ({t} : Set G) = D.Z := by
  classical
  have hle := card_inf_centralizer_le_of_not_mem D Ch h4 h23 h1930 c ht htC
  have hZcard : Nat.card D.Z = 2 ^ CFSG.Open.pRank 2 D.Z :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two
      (c.isElemAbelian_Z h4 h1930)
  rw [← hZcard] at hle
  have hZleV : D.Z ≤ c.V := uc22p22v_le_conjClosure c.N D.Z
  have hZleC : D.Z ≤ Subgroup.centralizer ({t} : Set G) := by
    intro z hz
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (uc22main1_T_le_centralizer D ht) z hz)
  exact (Subgroup.eq_of_le_of_card_ge (le_inf hZleV hZleC) hle).symm

theorem three_le_pRank_Z (D : Data G) (Ch : Choice2011 G)
    (hE : UC22P20gExcFacts) (h207 : S20_7 D) (h52 : S23_5_2 D Ch) (h23 : S23_23 D Ch)
    (h1930 : H1930 D) (c : Ctx23L D Ch) :
    3 ≤ CFSG.Open.pRank 2 D.Z := by
  have hn3 : 3 ≤ c.n := uc22p20g_hn3_of hE D Ch h207 h1930 c.toCtx23.toCtx21
  rwa [c.n_eq_pRank h52 h23 h1930] at hn3

structure S2341Frame (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch) where
  F : Subgroup G
  hFE : F ≤ c.E
  hFindex : (F.subgroupOf c.E).index ≤ 2
  h : G
  hF : F ≤ conjSubgroup D.T h
  W : Subgroup G
  hW : W = conjSubgroup c.V h
  Zh : Subgroup G
  hZh : Zh = conjSubgroup D.Z h

namespace S2341Frame

theorem card_W {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) :
    Nat.card X.W = (2 ^ CFSG.Open.pRank 2 D.Z) ^ 2 := by
  rw [X.hW, E3.card_conjSubgroup, card_V_eq D Ch h4 h23 h1930 c]

theorem isElemAbelian_W {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h1930 : H1930 D) :
    IsElemAbelian 2 X.W := by
  rw [X.hW]
  exact E3.isElemAbelian_conjSubgroup (c.isElemAbelian_V h4 h1930) X.h

theorem relIndex_centralizer_le {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h1930 : H1930 D) :
    (X.F ⊓ Subgroup.centralizer (X.W : Set G)).relIndex X.F ≤
      2 ^ CFSG.Open.pRank 2 D.Z := by
  have hF' : conjSubgroup X.F X.h⁻¹ ≤ D.T := by
    have := E3.conjSubgroup_mono_left X.h⁻¹ X.hF
    rwa [E3.conjSubgroup_conj_inv] at this
  have hconj : conjSubgroup (X.F ⊓ Subgroup.centralizer (X.W : Set G)) X.h⁻¹ =
      conjSubgroup X.F X.h⁻¹ ⊓ Subgroup.centralizer (c.V : Set G) := by
    rw [E3.conjSubgroup_inf, E3.conjSubgroup_centralizer, X.hW,
      E3.conjSubgroup_conj_inv]
  rw [← E3.relIndex_conjSubgroup (A := X.F ⊓ Subgroup.centralizer (X.W : Set G))
    (B := X.F) (g := X.h⁻¹), hconj]
  calc (conjSubgroup X.F X.h⁻¹ ⊓ Subgroup.centralizer (c.V : Set G)).relIndex
        (conjSubgroup X.F X.h⁻¹)
      ≤ (D.T ⊓ Subgroup.centralizer (c.V : Set G)).relIndex D.T :=
        relIndex_inf_le_relIndex_inf_of_le hF'
    _ = 2 ^ CFSG.Open.pRank 2 D.Z := c.relIndex_centralizer_V_eq D Ch h4 h23 h1930

private theorem conj_mem_T_not_mem_centralizer {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c)
    {a : G} (haF : a ∈ X.F)
    (haC : a ∉ Subgroup.centralizer (X.W : Set G)) :
    X.h * a * X.h⁻¹ ∈ D.T ∧
      X.h * a * X.h⁻¹ ∉ Subgroup.centralizer (c.V : Set G) := by
  constructor
  · exact CFSG.Quasithin.mem_conjSubgroup_iff.mp (X.hF haF)
  · intro ht
    apply haC
    rw [Subgroup.mem_centralizer_iff] at ht ⊢
    intro w hw
    rw [X.hW] at hw
    obtain ⟨v, hv, hwv⟩ := hw
    have hwv' : w = X.h⁻¹ * v * X.h := by
      simpa [MulAut.conj_apply] using hwv.symm
    rw [hwv']
    have hcomm : v * (X.h * a * X.h⁻¹) = (X.h * a * X.h⁻¹) * v := ht v hv
    calc (X.h⁻¹ * v * X.h) * a
        = X.h⁻¹ * (v * (X.h * a * X.h⁻¹)) * X.h := by group
      _ = X.h⁻¹ * ((X.h * a * X.h⁻¹) * v) * X.h := by rw [← hcomm]
      _ = a * (X.h⁻¹ * v * X.h) := by group

private theorem conj_centralizer_singleton {D : Data G} {Ch : Choice2011 G}
    {c : Ctx23L D Ch} (X : S2341Frame D Ch c) (a : G) :
    conjSubgroup (Subgroup.centralizer ({a} : Set G)) X.h⁻¹ =
      Subgroup.centralizer ({X.h * a * X.h⁻¹} : Set G) := by
  ext x
  constructor
  · intro hx
    rw [CFSG.Quasithin.mem_conjSubgroup_iff] at hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h' : X.h⁻¹ * x * X.h * a = a * (X.h⁻¹ * x * X.h) := by
      simpa only [inv_inv] using hx
    calc x * (X.h * a * X.h⁻¹)
        = X.h * (X.h⁻¹ * x * X.h * a) * X.h⁻¹ := by group
      _ = X.h * (a * (X.h⁻¹ * x * X.h)) * X.h⁻¹ := by rw [h']
      _ = (X.h * a * X.h⁻¹) * x := by group
  · intro hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    rw [CFSG.Quasithin.mem_conjSubgroup_iff]
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [inv_inv]
    calc X.h⁻¹ * x * X.h * a
        = X.h⁻¹ * (x * (X.h * a * X.h⁻¹)) * X.h := by group
      _ = X.h⁻¹ * ((X.h * a * X.h⁻¹) * x) * X.h := by rw [hx]
      _ = a * (X.h⁻¹ * x * X.h) := by group

theorem centralizer_eq {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D)
    {a : G} (haF : a ∈ X.F)
    (haC : a ∉ Subgroup.centralizer (X.W : Set G)) :
    X.W ⊓ Subgroup.centralizer ({a} : Set G) = X.Zh := by
  obtain ⟨htT, htC⟩ := conj_mem_T_not_mem_centralizer X haF haC
  have hconjC := conj_centralizer_singleton X a
  have hconj : conjSubgroup (X.W ⊓ Subgroup.centralizer ({a} : Set G)) X.h⁻¹ =
      c.V ⊓ Subgroup.centralizer ({X.h * a * X.h⁻¹} : Set G) := by
    rw [E3.conjSubgroup_inf, X.hW, E3.conjSubgroup_conj_inv, hconjC]
  rw [inf_centralizer_eq_Z_of_mem_T D Ch h4 h23 h1930 c htT htC] at hconj
  have h := congrArg (fun H : Subgroup G => conjSubgroup H X.h) hconj
  rw [E3.conjSubgroup_inv_conj] at h
  simpa [X.hZh] using h

theorem commutator_mem {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D)
    {a w : G} (haF : a ∈ X.F) (hwW : w ∈ X.W) :
    a * w * a⁻¹ * w⁻¹ ∈ X.Zh := by
  have htT : X.h * a * X.h⁻¹ ∈ D.T :=
    CFSG.Quasithin.mem_conjSubgroup_iff.mp (X.hF haF)
  have hwV : X.h * w * X.h⁻¹ ∈ c.V := by
    rw [X.hW] at hwW
    exact CFSG.Quasithin.mem_conjSubgroup_iff.mp hwW
  have hcomm := commutator_mem_Z_of_mem_T D Ch h4 h23 h1930 c htT hwV
  rw [X.hZh, CFSG.Quasithin.mem_conjSubgroup_iff]
  have heq : X.h * (a * w * a⁻¹ * w⁻¹) * X.h⁻¹ =
      (X.h * a * X.h⁻¹) * (X.h * w * X.h⁻¹) * (X.h * a * X.h⁻¹)⁻¹ *
        (X.h * w * X.h⁻¹)⁻¹ := by group
  rwa [heq]

theorem W_le_pCore {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h39 : S23_39 D Ch) (h1930 : H1930 D) :
    X.W ≤ conjSubgroup (CFSG.Open.pCoreOf 2 D.M) X.h := by
  rw [X.hW]
  exact E3.conjSubgroup_mono_left X.h
    ((uc22p22v_le_conjClosure D.M c.V).trans (c.E_le_pCoreOf_M h39 h1930))

theorem centralizer_le {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (X : S2341Frame D Ch c) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    {z : G} (hzZ : z ∈ X.Zh) (hz1 : z ≠ 1) :
    Subgroup.centralizer ({z} : Set G) ≤ conjSubgroup D.M X.h := by
  rw [X.hZh] at hzZ
  have hz₀Z : X.h * z * X.h⁻¹ ∈ D.Z :=
    CFSG.Quasithin.mem_conjSubgroup_iff.mp hzZ
  have hz₀1 : X.h * z * X.h⁻¹ ≠ 1 := by
    intro h0
    apply hz1
    have := congrArg (fun y : G => X.h⁻¹ * y * X.h) h0
    have h2 : X.h⁻¹ * (X.h * z * X.h⁻¹) * X.h = z := by group
    rw [h2] at this
    have h3 : z = 1 := by simpa using this
    exact h3
  have hC : Subgroup.centralizer ({X.h * z * X.h⁻¹} : Set G) ≤ D.M :=
    Data.centralizer_le_of_mem_U D c.hTI ((h4 h1930 c).1 ▸ hz₀Z) hz₀1
  intro c hc
  rw [CFSG.Quasithin.mem_conjSubgroup_iff]
  apply hC
  rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
  calc (X.h * c * X.h⁻¹) * (X.h * z * X.h⁻¹)
      = X.h * (c * z) * X.h⁻¹ := by group
    _ = X.h * (z * c) * X.h⁻¹ := by rw [hc]
    _ = (X.h * z * X.h⁻¹) * (X.h * c * X.h⁻¹) := by group

end S2341Frame

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22
