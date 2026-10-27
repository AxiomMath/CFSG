module

public import CFSG.Quasithin.EmptyFaithful.SBd9LieDef
public import CFSG.Quasithin.EmptyFaithful.S153D35

public section

namespace CFSG.Quasithin.SBd9

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem pCoreOf_eq_of_normalizes {Q X : Subgroup G} (hQ : IsSylowTwoOf Q L) (hQX : Q ≤ X)
    (hXL : X ≤ L) (hXN : X ≤ Subgroup.normalizer (Q : Set G)) : pCoreOf 2 X = Q := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm ?_ (le_pCoreOf_of_le_normalizer 2 hQX hXN hQ.2.1)
  exact (A4.isSylowTwoOf_iff_maximal.mp hQ).2.2 (pCoreOf 2 X) ((pCoreOf_le 2 X).trans hXL)
    (pCoreOf_isPGroup 2 X) (le_pCoreOf_of_le_normalizer 2 hQX hXN hQ.2.1)

theorem normalizer_le_normalizer_of_normal_sylow {Q X : Subgroup G} (hQ : IsSylowTwoOf Q L)
    (hQX : Q ≤ X) (hXL : X ≤ L) (hXN : X ≤ Subgroup.normalizer (Q : Set G)) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (Q : Set G) := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := normalizer_le_normalizer_pCoreOf 2 X
  rwa [pCoreOf_eq_of_normalizes hQ hQX hXL hXN] at h


omit [Finite G] in
theorem Sgp_le_normalizer_L (hL0 : L = conjClosure L (Sgp153 T V₁)) :
    Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := by
  have := le_normalizer_conjClosure L (Sgp153 T V₁)
  rwa [← hL0] at this

theorem sylow_inf_Sgp (c : CtxComp2 T Mc M V₁ V₂ Yp I L t)
    (hL0 : L = conjClosure L (Sgp153 T V₁)) : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L := by
  have hLI : L ≤ I := le_of_mem_cComp c.c33.mem
  have hSL := Sgp_le_normalizer_L hL0
  have hSyl := c.facts.sylow
  exact A4.isSylowTwoOf_inf_normal (A4.isSylowTwoOf_mono hSyl (le_inf hSyl.1 hSL) inf_le_left)
    (le_inf hLI Subgroup.le_normalizer) inf_le_right

theorem borel_stage (h37 : A37ForSQTK) (h38 : A38ForSQTK) (c : CtxComp2 T Mc M V₁ V₂ Yp I L t)
    (hL0 : L = conjClosure L (Sgp153 T V₁)) {q : ℕ} (hLie : LieL3 L (Sgp153 T V₁ ⊓ L) q) :
    Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) := by
  have hQ := sylow_inf_Sgp c hL0
  have hYN : Yp ≤ Subgroup.normalizer (L : Set G) :=
    S153D.Yp_le_normalizer h37 h38 c.hyp c.inH c.c33.mem
  have hSL := Sgp_le_normalizer_L hL0
  have hYSL : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := sup_le hYN hSL
  have hQX : Sgp153 T V₁ ⊓ L ≤ (Yp ⊔ Sgp153 T V₁) ⊓ L :=
    le_inf (inf_le_left.trans le_sup_right) inf_le_right
  have hXY : (Yp ⊔ Sgp153 T V₁) ⊓ L ≤ Yp ⊔ Sgp153 T V₁ := inf_le_left
  have hsolv : Group.IsSolvable ↥((Yp ⊔ Sgp153 T V₁) ⊓ L) := by
    have : Group.IsSolvable ↥(Yp ⊔ Sgp153 T V₁) := S153D.isSolvable_Yp_sup c.hyp c.inH c.facts11
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hXY)
      (Subgroup.inclusion_injective hXY)
  have hXQ := hLie.solv _ hQX inf_le_right hsolv
  have hNX := normalizer_le_normalizer_of_normal_sylow hQ hQX inf_le_right hXQ
  intro g hg
  exact hNX (Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hYSL hg⟩)


theorem sylow_le_centralizer_V (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hL0 : L = conjClosure L (Sgp153 T V₁)) {q : ℕ}
    (hLie : LieL3 L (Sgp153 T V₁ ⊓ L) q) :
    Sgp153 T V₁ ⊓ L ≤ Subgroup.centralizer (VZ T M : Set G) := by
  have hQ := sylow_inf_Sgp c hL0
  have hQn := borel_stage h37 h38 c hL0 hLie
  have h1 : Sgp153 T V₁ ⊓ L ≤ R153 T V₁ Yp :=
    le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_right) hQn hQ.2.1
  rw [c.facts11.R_eq] at h1
  exact h1.trans inf_le_right

theorem borel_le_MI (h37 : A37ForSQTK) (h38 : A38ForSQTK) (c : CtxComp2 T Mc M V₁ V₂ Yp I L t)
    (hL0 : L = conjClosure L (Sgp153 T V₁)) {q : ℕ} (hLie : LieL3 L (Sgp153 T V₁ ⊓ L) q) :
    L ⊓ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) ≤ M ⊓ I := by
  have hQ := sylow_inf_Sgp c hL0
  have hQn := borel_stage h37 h38 c hL0 hLie
  have hYN : Yp ≤ Subgroup.normalizer (L : Set G) :=
    S153D.Yp_le_normalizer h37 h38 c.hyp c.inH c.c33.mem
  have hSL := Sgp_le_normalizer_L hL0
  have hYSL : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := sup_le hYN hSL
  have hBX : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer
      ((L ⊓ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) : Subgroup G) : Set G) :=
    fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨hYSL hg, Subgroup.le_normalizer (hQn hg)⟩
  have hBpc : pCoreOf 2 (L ⊓ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G)) =
      Sgp153 T V₁ ⊓ L :=
    pCoreOf_eq_of_normalizes hQ (le_inf hQ.1 Subgroup.le_normalizer) inf_le_left inf_le_right
  have hChar : CharTwo (L ⊓ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G)) := by
    intro x hx
    rw [hBpc] at hx ⊢
    exact hLie.cent ⟨hx.1.1, hx.2⟩
  exact c.c33.inv_le _ (inf_le_left.trans (le_of_eq hL0)) hBX hChar

theorem MI_le_normalizer_Yp (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) :
    M ⊓ I ≤ Subgroup.normalizer (Yp : Set G) := fun x hx => by
  have : x ∈ I ⊓ Subgroup.normalizer (Yp : Set G) := by rw [c.facts.norm_eq]; exact hx
  exact this.2

theorem pow72_mem_centralizer (hh : Hyp15310 G T Mc M V₁ V₂ Yp t) {g : G} (hg : g ∈ M) :
    g ^ 72 ∈ Subgroup.centralizer (VZ T M : Set G) := by
  obtain ⟨hV, L₁, L₂, tb, hS, -⟩ := hh.decomp.model
  have hcard : Nat.card ↥(autI hV M) = 72 := hS.card_X
  have hgN : g ∈ Subgroup.normalizer (VZ T M : Set G) := hh.hyp.le_normalizer hg
  have hmem : convI hV ⟨g, hgN⟩ ∈ autI hV M := convI_mem_autI hV hg hgN
  have h1 : (⟨convI hV ⟨g, hgN⟩, hmem⟩ : ↥(autI hV M)) ^ 72 = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  have h2 : convI hV ⟨g, hgN⟩ ^ 72 = 1 := by
    have := congrArg Subtype.val h1
    simpa using this
  have h3 : convI hV ((⟨g, hgN⟩ : ↥(Subgroup.normalizer (VZ T M : Set G))) ^ 72) = 1 := by
    rw [map_pow]
    exact h2
  have h4 := (convI_eq_one_iff hV _).mp h3
  simpa using h4


omit [Finite G] in
theorem VZ_le_Sgp153 [Finite G] (hh : Hyp15310 G T Mc M V₁ V₂ Yp t) : VZ T M ≤ Sgp153 T V₁ := by
  intro v hv
  refine ⟨hh.hyp.VZ_le_T hv, A4.mem_normalizer_of_conj_mem fun k hk => ?_⟩
  have hc := congrArg Subtype.val
    (hh.hyp.elemAbelian.1.is_comm.comm ⟨v, hv⟩ ⟨k, hh.decomp.le₁ hk⟩)
  have : v * k * v⁻¹ = k := by
    have h1 : v * k = k * v := hc
    rw [h1]
    group
  rw [this]
  exact hk

theorem Yp_le_MI (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) : Yp ≤ M ⊓ I := by
  intro y hy
  have h1 : y ∈ I ⊓ Subgroup.normalizer (Yp : Set G) :=
    ⟨le_sup_left.trans c.inH.1.1 hy, Subgroup.le_normalizer hy⟩
  rw [c.facts.norm_eq] at h1
  exact h1

end CFSG.Quasithin.SBd9
