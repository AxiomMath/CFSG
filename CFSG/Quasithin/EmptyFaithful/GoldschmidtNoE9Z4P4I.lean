module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4U
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4IUK
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4IFus
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P4ISing

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.S1417
open scoped commutatorElement

section I

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ} {R₁ R₂ : Subgroup G}
  {s : G}

theorem e9z4_isI (h35 : Lemma1435) (h5 : Stage1461Five) (h2 : Stage1461Two)
    (h4 : Stage1463Four) (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ p) (hmax : PMaximal T M p) (hshape : IsE9Z4Shape T H p)
    (hdat : IsE9Dat T M H PQ R₁ R₂ s) (hF : oTwoUpper H ≤ oTwoFstarIn (mcOf T))
    (h16 : Subgroup.normalizer ((T ⊓ Subgroup.normalizer (R₁ : Set G) : Subgroup G) : Set G) ⊓
      mcOf T = T)
    {u : G} (hu : u ∈ uHi T M H R₁ ∨ u ∈ uHi T M H R₂) (huZ : u ∉ quasithinOmegaOneCenter T)
    (huT : T ⊓ Subgroup.normalizer (R₁ : Set G) ≤ tZero T u) :
    IsI T M u (Subgroup.centralizer ({u} : Set G)) := by
  classical
  have _hmax : PMaximal T M p := hmax
  have hH : IsHTM T M H := hred.isHTM
  have hInv : IsInvU T M H u := e9z4_isInvU h35 h5 S hred hmax hshape hdat hF h16 hu huZ huT
  have h1 := stage1463_one_proof G T M S H hH u hInv
  have h4' := h4 G T M S H hH u hInv
  have hR₁H : R₁ ≤ H := hdat.plane₁.2.1.trans hred.le
  have hR₂H : R₂ ≤ H := hdat.plane₂.2.1.trans hred.le
  have huU : u ∈ conjClosure (VZ T M) H := hInv.mem
  have hu1 : u ≠ 1 := fun h' => huZ (h' ▸ (quasithinOmegaOneCenter T).one_mem)
  have hZK := e9_Z_le_uK h5 S hred
  have huK : u ∈ uK T M H := by
    rcases hu with hu | hu
    · exact (sup_le (Subgroup.commutator_mono le_rfl hR₁H) hZK) hu
    · exact (sup_le (Subgroup.commutator_mono le_rfl hR₂H) hZK) hu
  have hUK := e9_exists_conj_uK h35 h5 S hred hshape hdat hu huZ h1.2.1
  obtain ⟨h98, hsplit, Q₁, Q₂, hstr, hpp, hR₁eq, hR₂eq⟩ := hdat.setup h35 S hred hshape
  subst hR₁eq hR₂eq
  have hTrans : ∀ u u' : G,
      (u ∈ uHi T M H (HLb (resBeta (rhoH h98.toHypF91)) Q₁) ∨
        u ∈ uHi T M H (HLb (resBeta (rhoH h98.toHypF91)) Q₂)) →
      u ∉ quasithinOmegaOneCenter T →
      (u' ∈ uHi T M H (HLb (resBeta (rhoH h98.toHypF91)) Q₁) ∨
        u' ∈ uHi T M H (HLb (resBeta (rhoH h98.toHypF91)) Q₂)) →
      u' ∉ quasithinOmegaOneCenter T →
        ∃ c ∈ H, c * u * c⁻¹ * u'⁻¹ ∈ quasithinOmegaOneCenter T :=
    fun u u' hu huZ hu' hu'Z =>
      e9_exists_conj_of_mem_uHi S hH h98.toHypF91 hsplit hstr hpp hu huZ hu' hu'Z
  have hSing : ∀ w ∈ uK T M H, w ∉ uHi T M H (HLb (resBeta (rhoH h98.toHypF91)) Q₁) →
      w ∉ uHi T M H (HLb (resBeta (rhoH h98.toHypF91)) Q₂) →
        ∃ S' : Subgroup G, S' ≤ H ⊓ Subgroup.centralizer ({w} : Set G) ∧ IsPGroup 2 S' ∧
          Nat.card T ≤ 2 * Nat.card S' :=
    fun w hwK hw₁ hw₂ =>
      e9_exists_twoGroup_of_singular S hH h98.toHypF91 hsplit hstr hpp hshape.2 hwK hw₁ hw₂
  refine ⟨S.inH_centralizer hH huU hu1, ?_, ?_⟩
  · exact e9_not_centralizer_le_mcOf S hH hR₁H hR₂H hTrans hSing huK hu huZ ⟨h1.1, h1.2.1⟩
      ⟨h4'.2.1, h4'.2.2⟩ hUK
  · rcases hu with hu | hu
    · exact e9_not_centralizer_le_M S h2 hred hdat.plane₂ hdat.cent₁ hu
    · exact e9_not_centralizer_le_M S h2 hred hdat.plane₁ hdat.cent₂ hu

end I

end CFSG.Quasithin
