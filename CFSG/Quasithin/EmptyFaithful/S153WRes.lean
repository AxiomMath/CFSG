module

public import CFSG.Quasithin.EmptyFaithful.S153WSeven
public import CFSG.Quasithin.EmptyFaithful.ModFA5Cfg
public import CFSG.Quasithin.EmptyFaithful.S153WCent2

public section

namespace CFSG.QuasithinUnique.AppCS2W

open CFSG.QuasithinUnique.AppCS2 CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.DoubleA3 Equiv Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H S L : Subgroup G}

namespace WTwo

variable {t x : G} (X : WTwo H S L t x)
include X

theorem blockD_le_centerOf_baum : blockD S L ≤ centerOf (baum S) := by
  intro d hd
  refine ⟨X.blockD_le_baum hd, Subgroup.mem_centralizer_iff.2 fun b hb => ?_⟩
  have hab := C5.isElemAbelian_two_iff.mp X.blockD_isElemAbelian
  have hU0 : blockU0 S L = U0 L t := X.C.D.blockU0_eq
  have hle : baum S ≤ Subgroup.centralizer ({d} : Set G) := by
    rw [X.baum_eq]
    refine sup_le (sup_le ?_ ?_) ?_
    · intro g hg
      rw [X.baumD_eq_blockD] at hg
      exact Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff.mp hh]
        exact (hab.1 g hg d hd).symm
    · intro g hg
      rw [hU0] at hg
      exact Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff.mp hh]
        exact (X.U0_comm_blockD hd hg).symm
    · intro g hg
      rw [hU0, conjR_U0_eq L t x] at hg
      exact Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff.mp hh]
        exact (comm_sup_left (A₁ := conjR (blockU L) x) (A₂ := conjR (blockU2 L t) x)
          (B := blockD S L) (fun a ha b hb => (X.blockD_comm_V₁ hb ha).symm)
          (fun a ha b hb => (X.blockD_comm_V₂ hb ha).symm) g hg d hd).symm
  have := Subgroup.mem_centralizer_iff.1 (hle hb) d (Set.mem_singleton d)
  exact this.symm

end WTwo

end CFSG.QuasithinUnique.AppCS2W

namespace CFSG.Quasithin.ModF

open CFSG.QuasithinUnique.AppCS2W CFSG.QuasithinUnique.AppCS2 CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {I S Iz K₁ K₂ : Subgroup G}

namespace A5Cfg

variable (c : A5Cfg I S Iz K₁ K₂)
include c

omit [Finite G] in
theorem ne_of_comm (h : K₂ = K₁) : False := by
  have hL := c.blk₁.1
  have hlt : blockZ K₁ < blockU K₁ := hL.2.2.2.2.1
  have hU : blockU K₁ ≤ K₁ := (C1.blockQ_le K₁).trans' (C1.blockU_le_blockQ hL)
  refine hlt.not_ge fun u hu => ?_
  refine ⟨hu, Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
  exact c.comm k hk u (h ▸ hU hu)

theorem exists_wdbl (ht : ∃ t ∈ S, B6.conjSub t K₁ = K₂) (hJ : ⁅K₁, thompsonJ S⁆ = K₁) :
    ∃ t : G, Nonempty (WDbl I S K₁ t) := by
  obtain ⟨t, htS, htK⟩ := ht
  have hconj : conjR K₁ t⁻¹ = K₂ := by
    show K₁.map (MulAut.conj (t⁻¹)⁻¹).toMonoidHom = K₂
    rw [inv_inv]
    exact htK
  have hjoin : conjJoin S K₁ = K₁ ⊔ K₂ := by
    refine le_antisymm (iSup_le fun s => ?_) (sup_le (C56.le_conjJoin K₁ S.one_mem) ?_)
    · rcases c.perm₁ (s : G) s.2 with h | h
      · exact (le_of_eq h).trans le_sup_left
      · exact (le_of_eq h).trans le_sup_right
    · rw [← hconj]
      exact DoubleA3.conjR_le_conjJoin' (S.inv_mem htS)
  have hcomm : ⁅K₁, K₂⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    exact Subgroup.mem_centralizer_iff.2 fun b hb => (c.comm a ha b hb).symm
  refine ⟨t⁻¹, ⟨⟨⟨c.sylow, ⟨c.blk₁, Or.inr (Or.inr c.a5₁)⟩, hJ, ?_⟩, c.a5₁, S.inv_mem htS, ?_, ?_, ?_⟩⟩⟩
  · rw [hjoin, c.gen, sup_comm]
  · rw [hconj]
    exact fun h => c.ne_of_comm h
  · rw [hconj]
    exact hjoin
  · rw [hconj]
    exact hcomm

theorem elemAbelian_and_le_centerOf_baum {Λ : Subgroup G} (ht : ∃ t ∈ S, B6.conjSub t K₁ = K₂)
    (hJ : ⁅K₁, thompsonJ S⁆ = K₁) (hΛ : Λ ≤ Subgroup.normalizer (S : Set G)) (hSΛ : S ≤ Λ)
    (hrel : S.relIndex Λ = 2)
    (hb : ∀ R₀ : Subgroup G, R₀ ≤ S → R₀ ≠ ⊥ → ¬ (Λ ⊔ I ≤ Subgroup.normalizer (R₀ : Set G))) :
    CFSG.Open.IsElemAbelian 2 (S ⊓ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G)) ∧
      S ⊓ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) ≤ centerOf (baum S) := by
  obtain ⟨t, ⟨D⟩⟩ := c.exists_wdbl ht hJ
  have hC52 : C5.NoCommonNormal S I Λ := fun X hXS hXne hIX hΛX =>
    hb X hXS hXne (sup_le hΛX hIX)
  obtain ⟨x, hxΛ, hxS, hgood⟩ := D.exists_good hC52 hSΛ hrel
  have hxN : x ∈ normalizer (S : Set G) := hΛ hxΛ
  obtain ⟨C⟩ := D.nonempty_cfg
  obtain ⟨C'⟩ := D.swap.nonempty_cfg
  let X : WTwo I S K₁ t x := ⟨C, C', hxN, hgood, Λ, hSΛ, hC52, hrel, hxΛ, hxS⟩
  have hjoin : conjJoin S K₁ = K₁ ⊔ K₂ := by
    obtain ⟨t₀, ht₀, htK₀⟩ := ht
    refine le_antisymm (iSup_le fun s => ?_) (sup_le (C56.le_conjJoin K₁ S.one_mem) ?_)
    · rcases c.perm₁ (s : G) s.2 with h | h
      · exact (le_of_eq h).trans le_sup_left
      · exact (le_of_eq h).trans le_sup_right
    · have : conjR K₁ t₀⁻¹ = K₂ := by
        show K₁.map (MulAut.conj (t₀⁻¹)⁻¹).toMonoidHom = K₂
        rw [inv_inv]
        exact htK₀
      rw [← this]
      exact DoubleA3.conjR_le_conjJoin' (S.inv_mem ht₀)
  have hD : S ⊓ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) = blockD S K₁ := by
    rw [blockD, hjoin]
  rw [hD]
  exact ⟨X.blockD_isElemAbelian, X.blockD_le_centerOf_baum⟩

end A5Cfg

end CFSG.Quasithin.ModF
