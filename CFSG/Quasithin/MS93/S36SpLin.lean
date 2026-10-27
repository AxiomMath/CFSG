module

public import CFSG.Quasithin.MS93.S36SpFrame

public section

namespace CFSG.Quasithin.MS93.S36SP

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93.MSP
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {h : PUHyp M T L}

theorem pow_eq_one_of_mem_T (h : PUHyp M T L) {t : G} (ht : t ∈ T) : ∃ e : ℕ, t ^ 2 ^ e = 1 := by
  obtain ⟨e, he⟩ := h.isPGroup ⟨t, ht⟩
  exact ⟨e, by simpa using congrArg Subtype.val he⟩

namespace SpFrame

variable (d : SpFrame h)

theorem normU (_d : SpFrame h) : M ≤ Subgroup.normalizer (Uq M T L : Set G) :=
  le_normalizer_Uq h.le_normalizer

theorem card_F : Nat.card d.F = 2 ^ d.k := by rw [Nat.card_eq_fintype_card, d.card]

theorem exists_add {t : G} (ht : t ∈ M) :
    ∃ f : V4 d.F →+ V4 d.F, Function.Bijective f ∧ Normalizes f ∧ ActsAdd d.vec t f := by
  obtain ⟨f, hfb, hf⟩ := exists_actsAdd d.surj (C := Zq M L) d.ker (d.normU ht)
    (le_normalizer_Zq h.le_normalizer ht)
  refine ⟨f, hfb, normalizes_of_actsAdd d.surj (d.normU ht) hf fun g => ?_, hf⟩
  obtain ⟨x, hxM, hxg, hconj⟩ := d.gen g
  exact ⟨x, d.normU hxM, hxg, hconj t ht⟩

theorem exists_actsMat {t : G} (ht : t ∈ M) (ht2 : ∃ e : ℕ, t ^ 2 ^ e = 1)
    {f : V4 d.F →+ V4 d.F} (hfb : Function.Bijective f) (hfn : Normalizes f)
    (hf : ActsAdd d.vec t f) (hlin : ∀ (c : d.F) (v : V4 d.F), f (c • v) = c • f v) :
    ∃ g : Sp4 d.F, ActsMat d.vec t g := by
  obtain ⟨e, he⟩ := ht2
  exact exists_actsMat_of_linear d.surj (d.normU ht) hf hfb hfn hlin he

theorem card_le_fixAdd {t : G} {f : V4 d.F →+ V4 d.F} (hf : ActsAdd d.vec t f) :
    Nat.card (V4 d.F) ≤ Nat.card (CFSG.Quasithin.Vol2.KGNat.fixAdd f) *
      (Subgroup.centralizer ({t} : Set G)).relIndex (Uq M T L) := by
  set S : Subgroup (Multiplicative (V4 d.F)) :=
    (CFSG.Quasithin.Vol2.KGNat.fixAdd f).toSubgroup with hS
  have hK : (Subgroup.centralizer ({t} : Set G)).subgroupOf (Uq M T L) ≤ S.comap d.vec := by
    intro u hu
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hu
    have htu : t * u * t⁻¹ = u := by
      rw [hu t rfl, mul_inv_cancel_right]
    have h1 := hf u u htu.symm
    show f (Multiplicative.toAdd (d.vec u)) = Multiplicative.toAdd (d.vec u)
    exact h1.symm
  have hidx : S.index ≤ (Subgroup.centralizer ({t} : Set G)).relIndex (Uq M T L) := by
    rw [← Subgroup.index_comap_of_surjective S d.surj]
    exact Subgroup.index_antitone hK
  have hcard : Nat.card (V4 d.F) = Nat.card S * S.index := by
    rw [Subgroup.card_mul_index]
    rfl
  have hS' : Nat.card S = Nat.card (CFSG.Quasithin.Vol2.KGNat.fixAdd f) := rfl
  rw [hcard, hS']
  exact Nat.mul_le_mul_left _ hidx

theorem exists_actsMat_of_relIndex {t : G} (ht : t ∈ M) (ht2 : ∃ e : ℕ, t ^ 2 ^ e = 1)
    (hidx : (Subgroup.centralizer ({t} : Set G)).relIndex (Uq M T L) ≤ 2 ^ d.k) :
    ∃ g : Sp4 d.F, ActsMat d.vec t g := by
  obtain ⟨f, hfb, hfn, hf⟩ := d.exists_add ht
  refine d.exists_actsMat ht ht2 hfb hfn hf (linear_of_card hfb hfn ?_)
  have h1 := d.card_le_fixAdd hf
  rw [card_V4, d.card_F] at h1
  set c := Nat.card (CFSG.Quasithin.Vol2.KGNat.fixAdd f)
  have hq : 2 ≤ 2 ^ d.k := Nat.le_self_pow (by have := d.one_le; omega) 2
  have h2 : (2 ^ d.k) ^ 4 ≤ c * 2 ^ d.k := h1.trans (Nat.mul_le_mul_left _ hidx)
  have h3 : (2 ^ d.k) ^ 3 ≤ c := by
    have hpos : 0 < 2 ^ d.k := by positivity
    have : (2 ^ d.k) ^ 3 * 2 ^ d.k ≤ c * 2 ^ d.k := by
      calc (2 ^ d.k) ^ 3 * 2 ^ d.k = (2 ^ d.k) ^ 4 := by ring
        _ ≤ c * 2 ^ d.k := h2
    exact Nat.le_of_mul_le_mul_right this hpos
  rw [card_V4, d.card_F]
  calc (2 ^ d.k) ^ 4 < (2 ^ d.k) ^ (3 * 2) :=
        Nat.pow_lt_pow_right (a := 2 ^ d.k) (by omega) (by norm_num)
    _ = ((2 ^ d.k) ^ 3) ^ 2 := by rw [pow_mul]
    _ ≤ c ^ 2 := Nat.pow_le_pow_left h3 2

theorem exists_actsMat_of_commute {t : G} (ht : t ∈ M) (ht2 : ∃ e : ℕ, t ^ 2 ^ e = 1)
    {a : V4 d.F} (ha : a ≠ 0)
    (hX : ∀ c : d.F, ∃ x ∈ M, ActsMat d.vec x (transv a c) ∧ t * x = x * t) :
    ∃ g : Sp4 d.F, ActsMat d.vec t g := by
  obtain ⟨f, hfb, hfn, hf⟩ := d.exists_add ht
  refine d.exists_actsMat ht ht2 hfb hfn hf (linear_of_commute_transv hfb hfn ha fun c v => ?_)
  obtain ⟨x, hxM, hxg, htx⟩ := hX c
  have h1 : ActsAdd d.vec (t * x) (f.comp (Matrix.mulVecLin (mat (transv a c))).toAddMonoidHom) :=
    actsAdd_mul (d.normU hxM) hf (actsMat_iff.1 hxg)
  have h2 : ActsAdd d.vec (x * t) ((Matrix.mulVecLin (mat (transv a c))).toAddMonoidHom.comp f) :=
    actsAdd_mul (d.normU ht) (actsMat_iff.1 hxg) hf
  rw [htx] at h1
  have := actsAdd_unique d.surj (d.normU (M.mul_mem hxM ht)) h1 h2
  exact DFunLike.congr_fun this v

@[expose] noncomputable def img (E : Subgroup G) (hEM : E ≤ M)
    (hE : ∀ e ∈ E, ∃ g, ActsMat d.vec e g) : Subgroup (Sp4 d.F) :=
  (rho d.surj E (hEM.trans d.normU) hE).range

variable {E : Subgroup G} (hEM : E ≤ M) (hE : ∀ e ∈ E, ∃ g, ActsMat d.vec e g)

theorem mem_img {g : Sp4 d.F} : g ∈ d.img E hEM hE ↔ ∃ e ∈ E, ActsMat d.vec e g := by
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e, e.2, actsMat_rho d.surj _ hE e⟩
  · rintro ⟨e, he, hg⟩
    exact ⟨⟨e, he⟩, rho_eq d.surj _ hE hg⟩

theorem actsMat_mem_img {e : G} (he : e ∈ E) {g : Sp4 d.F} (hg : ActsMat d.vec e g) :
    g ∈ d.img E hEM hE :=
  (d.mem_img hEM hE).2 ⟨e, he, hg⟩

theorem mem_centralizer_iff (u : ↥(Uq M T L)) :
    (u : G) ∈ Subgroup.centralizer (E : Set G) ↔
      Multiplicative.toAdd (d.vec u) ∈ fixSp (d.img E hEM hE) := by
  constructor
  · intro hu g hg
    obtain ⟨e, he, heg⟩ := (d.mem_img hEM hE).1 hg
    have heu : e * u * e⁻¹ = u := by
      rw [Subgroup.mem_centralizer_iff.1 hu e he, mul_inv_cancel_right]
    rw [← heg u u heu.symm]
  · intro hu
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    obtain ⟨g, hg⟩ := hE e he
    have hv := conj_mem (d.normU (hEM he)) u
    have h1 := hg u ⟨_, hv⟩ rfl
    rw [hu g (d.actsMat_mem_img hEM hE he hg)] at h1
    have h2 : d.vec (⟨_, hv⟩ * u⁻¹) = 1 := by
      rw [map_mul, map_inv]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_inv, h1, add_neg_cancel]
      rfl
    have h3 := d.lift e (hEM he) g hg u ((d.ker _).1 h2)
    calc e * u = e * u * e⁻¹ * e := by group
      _ = u * e := by rw [h3]

theorem card_img (hET : E ≤ T) :
    Nat.card (d.img E hEM hE) = (pCoreOf 2 M).relIndex E := by
  set ρ := rho d.surj E (hEM.trans d.normU) hE
  have hker : ρ.ker = (pCoreOf 2 M).subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro he
      have h1 : ActsMat d.vec e 1 := by
        have := actsMat_rho d.surj (hEM.trans d.normU) hE e
        rwa [show rho d.surj E (hEM.trans d.normU) hE e = 1 from he] at this
      exact mem_pCoreOf_of_mem_trivW h (hET e.2) (mem_trivW_of_actsMat_one h d.ker (hEM e.2) h1)
    · intro he
      refine actsMat_unique d.surj (d.normU (hEM e.2)) (actsMat_rho d.surj _ hE e) ?_
      intro u v huv
      have hc := h.pCoreOf_le_centralizer_Z0q he
      have : (v : G) = u := by
        rw [huv, ← Subgroup.mem_centralizer_iff.1 hc u (Uq_le_Z0q h.L_le u.2),
          mul_inv_cancel_right]
      rw [Subtype.ext this, mat_one, Matrix.one_mulVec]
  calc Nat.card (d.img E hEM hE) = Nat.card ρ.range := rfl
    _ = ρ.ker.index := (Subgroup.index_ker ρ).symm
    _ = (pCoreOf 2 M).relIndex E := by rw [hker]; rfl

theorem card_V4_eq :
    Nat.card (V4 d.F) = Nat.card (fixSp (d.img E hEM hE)) *
      (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) := by
  set S : Subgroup (Multiplicative (V4 d.F)) := (fixSp (d.img E hEM hE)).toAddSubgroup.toSubgroup
    with hS
  have hK : (Subgroup.centralizer (E : Set G)).subgroupOf (Uq M T L) = S.comap d.vec := by
    ext u
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, d.mem_centralizer_iff hEM hE u]
    rfl
  have hidx : S.index = (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) := by
    rw [← Subgroup.index_comap_of_surjective S d.surj, ← hK]
    rfl
  have hcard : Nat.card (V4 d.F) = Nat.card S * S.index := by
    rw [Subgroup.card_mul_index]
    rfl
  rw [hcard, hidx]
  rfl

theorem isPGroup_img (hET : E ≤ T) : IsPGroup 2 (d.img E hEM hE) := by
  have hE2 : IsPGroup 2 ↥E := h.isPGroup.to_le hET
  exact hE2.of_surjective _ (rho d.surj E (hEM.trans d.normU) hE).rangeRestrict_surjective

@[expose] noncomputable def pre (W' : Submodule d.F (V4 d.F)) : Subgroup G :=
  (W'.toAddSubgroup.toSubgroup.comap d.vec).map (Uq M T L).subtype

theorem mem_pre {W' : Submodule d.F (V4 d.F)} {x : G} :
    x ∈ d.pre W' ↔ ∃ hx : x ∈ Uq M T L, Multiplicative.toAdd (d.vec ⟨x, hx⟩) ∈ W' := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u.2, hu⟩
  · rintro ⟨hx, hu⟩
    exact ⟨⟨x, hx⟩, hu, rfl⟩

theorem mem_pre_coe {W' : Submodule d.F (V4 d.F)} (u : ↥(Uq M T L)) :
    (u : G) ∈ d.pre W' ↔ Multiplicative.toAdd (d.vec u) ∈ W' := by
  rw [mem_pre]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨u.2, h⟩⟩

theorem pre_le (W' : Submodule d.F (V4 d.F)) : d.pre W' ≤ Uq M T L := fun _ hx =>
  (d.mem_pre.1 hx).1

theorem pre_mono {W' W'' : Submodule d.F (V4 d.F)} (hW : W' ≤ W'') : d.pre W' ≤ d.pre W'' :=
  fun _ hx => by
    obtain ⟨hxU, hx⟩ := d.mem_pre.1 hx
    exact d.mem_pre.2 ⟨hxU, hW hx⟩

theorem C_le_pre (W' : Submodule d.F (V4 d.F)) : Uq M T L ⊓ Zq M L ≤ d.pre W' := by
  intro c hc
  refine d.mem_pre.2 ⟨hc.1, ?_⟩
  rw [(d.ker ⟨c, hc.1⟩).2 hc.2]
  exact W'.zero_mem

theorem pre_le_centralizer {W' : Submodule d.F (V4 d.F)}
    (hW : W' ≤ fixSp (d.img E hEM hE)) : d.pre W' ≤ Subgroup.centralizer (E : Set G) := by
  intro x hx
  obtain ⟨hxU, hxW⟩ := d.mem_pre.1 hx
  exact (d.mem_centralizer_iff hEM hE ⟨x, hxU⟩).2 (hW hxW)

theorem toAdd_vec_comm {x : G} (hx : x ∈ M) {g : Sp4 d.F} (hg : ActsMat d.vec x g)
    (u : ↥(Uq M T L)) :
    Multiplicative.toAdd (d.vec ⟨x * u * x⁻¹ * (u : G)⁻¹,
      mul_mem (conj_mem (d.normU hx) u) (inv_mem u.2)⟩) =
        mat g *ᵥ Multiplicative.toAdd (d.vec u) - Multiplicative.toAdd (d.vec u) :=
  vec_commutator (d.normU hx) hg u

end SpFrame

end CFSG.Quasithin.MS93.S36SP
