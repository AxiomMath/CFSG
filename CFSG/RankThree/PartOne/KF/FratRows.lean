module

public import CFSG.RankThree.PartOne.KF.FratCore
public import CFSG.RankThree.PartOne.KF.RowCore
public import CFSG.RankThree.PartOne.S12.Sec12Three
import CFSG.RankThree.PartOne.S9.Planes.Basic

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.KFU

variable {G : Type} [Group G]

theorem mem_normalizer_zpowers_of_conj_mem [Finite G] {b y : G}
    (h : y * b * y⁻¹ ∈ Subgroup.zpowers b) :
    y ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
  have hle : (Subgroup.zpowers b).map (MulAut.conj y).toMonoidHom ≤ Subgroup.zpowers b := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ h i
  have heq : (Subgroup.zpowers b).map (MulAut.conj y).toMonoidHom = Subgroup.zpowers b :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj y).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have : y * g * y⁻¹ ∈ (Subgroup.zpowers b).map (MulAut.conj y).toMonoidHom := ⟨g, hg, rfl⟩
    rwa [heq] at this
  · intro hg
    rw [← heq] at hg
    obtain ⟨g', hg'b, hg'e⟩ := hg
    have : g' = g := (MulAut.conj y).injective (by simpa using hg'e)
    rwa [← this]

section Core

variable [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem Fus12Ctx.generic (ctx : Fus12Ctx G p A c L E) : Sec12TwoGeneric p c L E := by
  rcases ctx.facts.two with h | h
  · exact h
  · exfalso
    apply ctx.c_not_mem
    have hc : c ∈ (Subgroup.center L).map L.subtype := by
      rw [h.center_eq]
      exact Subgroup.mem_zpowers c
    obtain ⟨z, -, hz⟩ := hc
    rw [← hz]
    exact z.2

theorem Fus12Ctx.table_core (ctx : Fus12Ctx G p A c L E) : Table123Core p L (A ⊓ L) (E ⊓ L) := by
  have h := ctx.hyp
  have hG := ctx.generic
  exact
  { prime := h.prime
    five_le := Sec12Three.five_le h
    quasisimple := hG.quasisimple
    center_pPrime := hG.center_pPrime
    A₀_le := inf_le_right
    A₀_elem := Planes.isElementaryAbelian_of_le inf_le_left h.A_elem
    A₀_card := Sec12Three.card_A_inf_L h hG (Sec12Three.c_not_mem_L h hG.center_pPrime)
    A₀_invariant := Sec12Three.invariant_A_inf_L h hG
    F_le := inf_le_right
    F_elem := Planes.isElementaryAbelian_of_le inf_le_left h.E_elem
    A₀_le_F := inf_le_inf_right L h.A_le_E
    F_le_centralizer := fun f hf a ha => by
      have hfE := (Subgroup.mem_inf.1 hf).1
      have haA := (Subgroup.mem_inf.1 ha).1
      exact (Subgroup.mem_centralizer_iff.1 (h.E_le hfE) a haA)
    F_max := fun F' hF'L hF'el hF'c hFF' =>
      Sec12Three.F_max_generic h hG F' hF'L hF'el hF'c hFF' }

theorem Fus12Ctx.mem_normalizer_inf (ctx : Fus12Ctx G p A c L E) {n : G}
    (hn : n ∈ cNormalizer c ⊓ torusNormalizer E) :
    n ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) :=
  Subgroup.inf_normalizer_le_normalizer_inf ⟨hn.2, ctx.facts.twoB hn⟩

theorem Fus12Ctx.mem_torusNormalizer (ctx : Fus12Ctx G p A c L E) {l : G} (hl : l ∈ L)
    (hlF : l ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G)) : l ∈ torusNormalizer E := by
  have h := ctx.hyp
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := by
    obtain ⟨L', -, hL'⟩ := h.L_mem.2
    rw [← hL']
    exact Subgroup.map_subtype_le _
  have hlc : l ∈ cNormalizer c :=
    mem_cNormalizer_of_commute (Subgroup.mem_centralizer_singleton_iff.1 (hLc hl))
  have hE : E = (E ⊓ L) ⊔ Subgroup.zpowers c := ctx.generic.E_eq
  rw [torusNormalizer, hE]
  exact Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hlF, hlc⟩

end Core

@[expose] def KF1215Scalar (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → RowModel p L r →
    ∀ n ∈ cNormalizer c ⊓ torusNormalizer E, ∃ l ∈ L ⊓ torusNormalizer E, ∃ k : ℕ,
      ∀ f ∈ E ⊓ L, (l * n) * f * (l * n)⁻¹ = f ^ k

theorem kf1215Frat_of_scalar (hrow : ∀ r : ℕ, 1 ≤ r → r ≤ 12 → r ≠ 7 → r ≠ 11 →
    KF1215Scalar r) : KF1215Frat := by
  intro G _ _ p A c L E ctx b K I X P Q hL hC hF hout h7 g hg
  have h := ctx.hyp
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := by
    obtain ⟨L', -, hL'⟩ := h.L_mem.2
    rw [← hL']
    exact Subgroup.map_subtype_le _
  have hLH : L ≤ cNormalizer c := fun l hl =>
    mem_cNormalizer_of_commute (Subgroup.mem_centralizer_singleton_iff.1 (hLc hl))
  obtain ⟨x, hx, n, hn, hgxn⟩ := frat_core ctx hout g hg
  obtain ⟨r, hr1, hr12, hmodel, -⟩ := ctx.facts.three.2
  have hr7 : r ≠ 7 := fun h => h7 (h ▸ hmodel)
  have hr11 : r ≠ 11 := fun h11 => by
    subst h11
    have hZ := ctx.ten.2.2
    have h1 := hmodel.1
    have h2 := hmodel.2.1
    exact hZ ⟨1, by omega⟩
  obtain ⟨l, hl, k, hk⟩ := hrow r hr1 hr12 hr7 hr11 G p A c L E ctx hmodel n hn
  have hlc : l * c = c * l := Subgroup.mem_centralizer_singleton_iff.1 (hLc hl.1)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1
    ((Subgroup.mem_normalizer_iff.1 hn.1 c).1 (Subgroup.mem_zpowers c))
  have hxn : x * (n * c * n⁻¹) = (n * c * n⁻¹) * x := by
    rw [← hj]
    exact (Commute.zpow_right (show Commute x c from
      Subgroup.mem_centralizer_singleton_iff.1 hx) j).eq
  have hln : l * (n * c * n⁻¹) = (n * c * n⁻¹) * l := by
    rw [← hj]
    exact (Commute.zpow_right (show Commute l c from hlc) j).eq
  have hbE : b ∈ E ⊓ L := ⟨h.A_le_E hL.b_mem.1, hL.b_mem.2.1⟩
  refine ⟨l * n, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact (torusNormalizer E).mul_mem hl.2 hn.2
  ·
    refine mem_normalizer_zpowers_of_conj_mem ?_
    rw [hk b hbE]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers b) k
  · exact (cNormalizer c).mul_mem (hLH hl.1) hn.1
  · calc l * n * c * (l * n)⁻¹ = l * (n * c * n⁻¹) * l⁻¹ := by group
      _ = n * c * n⁻¹ := by rw [hln]; group
      _ = g * c * g⁻¹ := by
        rw [hgxn]
        calc n * c * n⁻¹ = x * (n * c * n⁻¹) * x⁻¹ := by rw [hxn]; group
          _ = x * n * c * (x * n)⁻¹ := by group

end CFSG.RankThree.PartOne
