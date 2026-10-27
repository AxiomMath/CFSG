module

public import CFSG.LocalAnalysis.StandardType.GGRankOneShared
public import CFSG.LocalAnalysis.StandardType.GGReflectionBasic
import CFSG.LocalAnalysis.StandardType.GGSecFiveBFixLine
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj
import CFSG.LocalAnalysis.StandardType.GGSharedInvolution
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G]

@[expose] def GGOriginalRankOneConjugate (p : ℕ) (L H Bs : Subgroup G)
    (r : MulAut ↥Bs) (S : Subgroup G) : Prop :=
  ∃ t ∈ ggAutomizer L Bs, GGIsReflection p t ∧
    ∃ n ∈ H, n ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∃ a : MulAut ↥Bs, (∀ b : ↥Bs, ((a b : ↥Bs) : G) = n * b * n⁻¹) ∧
        r = a * t * a⁻¹ ∧ S = (ggRankOneIn L Bs t).map (MulAut.conj n).toMonoidHom

@[expose] noncomputable def ggRankOneFrom (p : ℕ) (L H Bs : Subgroup G)
    (r : MulAut ↥Bs) : Subgroup G :=
  ⨆ (S : Subgroup G) (_ : GGOriginalRankOneConjugate p L H Bs r S), S

theorem GGOriginalRankOneConjugate.le_ggRankOneFrom {p : ℕ} {L H Bs S : Subgroup G}
    {r : MulAut ↥Bs} (h : GGOriginalRankOneConjugate p L H Bs r S) :
    S ≤ ggRankOneFrom p L H Bs r :=
  le_iSup_of_le S (le_iSup_of_le h le_rfl)

theorem ggRankOneFrom_le {p : ℕ} {L H Bs : Subgroup G} (hLH : L ≤ H) (r : MulAut ↥Bs) :
    ggRankOneFrom p L H Bs r ≤ H := by
  refine iSup_le fun S => iSup_le fun hS => ?_
  obtain ⟨t, -, -, n, hn, -, a, -, -, rfl⟩ := hS
  rintro z ⟨v, hv, rfl⟩
  have hvL : v ∈ L := (ggOTwoPrime_le _ hv).1
  exact H.mul_mem (H.mul_mem hn (hLH hvL)) (H.inv_mem hn)

theorem GGOriginalRankOneConjugate.map_conj {p : ℕ} {L H Bs S : Subgroup G}
    {r a : MulAut ↥Bs} {m : G} (hm : m ∈ H)
    (hmN : m ∈ Subgroup.normalizer (Bs : Set G))
    (ha : ∀ b : ↥Bs, ((a b : ↥Bs) : G) = m * b * m⁻¹)
    (h : GGOriginalRankOneConjugate p L H Bs r S) :
    GGOriginalRankOneConjugate p L H Bs (a * r * a⁻¹)
      (S.map (MulAut.conj m).toMonoidHom) := by
  obtain ⟨t, ht, htr, n, hn, hnN, v, hv, rfl, rfl⟩ := h
  refine ⟨t, ht, htr, m * n, H.mul_mem hm hn, Subgroup.mul_mem _ hmN hnN, a * v,
    ?_, ?_, ?_⟩
  · intro b
    rw [MulAut.mul_apply, ha, hv, mul_inv_rev]
    group
  · group
  · rw [Subgroup.map_map]
    congr 1
    ext z
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

private theorem ggRankOneFrom_map_conj_le {p : ℕ} {L H Bs : Subgroup G}
    {a : MulAut ↥Bs} {m : G} (hm : m ∈ H)
    (hmN : m ∈ Subgroup.normalizer (Bs : Set G))
    (ha : ∀ b : ↥Bs, ((a b : ↥Bs) : G) = m * b * m⁻¹) (r : MulAut ↥Bs) :
    (ggRankOneFrom p L H Bs r).map (MulAut.conj m).toMonoidHom ≤
      ggRankOneFrom p L H Bs (a * r * a⁻¹) := by
  simp only [ggRankOneFrom, Subgroup.map_iSup]
  refine iSup_le fun S => iSup_le fun hS => ?_
  exact (hS.map_conj hm hmN ha).le_ggRankOneFrom

theorem ggRankOneFrom_map_conj {p : ℕ} {L H Bs : Subgroup G}
    {a : MulAut ↥Bs} {m : G} (hm : m ∈ H)
    (hmN : m ∈ Subgroup.normalizer (Bs : Set G))
    (ha : ∀ b : ↥Bs, ((a b : ↥Bs) : G) = m * b * m⁻¹) (r : MulAut ↥Bs) :
    (ggRankOneFrom p L H Bs r).map (MulAut.conj m).toMonoidHom =
      ggRankOneFrom p L H Bs (a * r * a⁻¹) := by
  refine le_antisymm (ggRankOneFrom_map_conj_le hm hmN ha r) ?_
  have hback := ggRankOneFrom_map_conj_le (p := p) (L := L) (a := a⁻¹) (H.inv_mem hm)
    (Subgroup.inv_mem _ hmN) (by simpa only [inv_inv] using inv_apply_of_forall ha)
    (a * r * a⁻¹)
  have hr : a⁻¹ * (a * r * a⁻¹) * (a⁻¹)⁻¹ = r := by group
  rw [hr] at hback
  have hmap := Subgroup.map_mono (f := (MulAut.conj m).toMonoidHom) hback
  have hcomp : (MulAut.conj m).toMonoidHom.comp (MulAut.conj m⁻¹).toMonoidHom =
      MonoidHom.id G := by
    ext z
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply]
    group
  rw [Subgroup.map_map, hcomp, Subgroup.map_id] at hmap
  exact hmap

section Components

variable [Finite G] {p : ℕ} {L H Bs : Subgroup G} {x : G}

theorem GGOriginalRankOneConjugate.component_data
    (hpp : p.Prime) (hBs : IsElemAbelian p Bs) (hx : x ∈ Bs)
    (hL : IsSubnormal L (Subgroup.centralizer ({x} : Set G)))
    (hBL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hqs : ∀ t ∈ ggAutomizer L Bs, GGIsReflection p t →
      CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn L Bs t))
    {r : MulAut ↥Bs} {S : Subgroup G} (h : GGOriginalRankOneConjugate p L H Bs r S) :
    IsComponentOf S (Subgroup.centralizer (ggHyperplane Bs r : Set G)) ∧
      Bs ≤ Subgroup.normalizer (S : Set G) ∧ r ∈ ggAutomizer S Bs ∧ r ^ 2 = 1 ∧ r ≠ 1 := by
  obtain ⟨t, ht, htr, n, -, hn, a, ha, rfl, rfl⟩ := h
  have hxH : x ∈ ggHyperplane Bs t := by
    obtain ⟨g, hgL, -, hg⟩ := mem_ggAutomizer_iff.mp ht
    refine Subgroup.mem_map.mpr ⟨⟨x, hx⟩, ?_, rfl⟩
    change t ⟨x, hx⟩ = ⟨x, hx⟩
    apply Subtype.ext
    rw [hg, Subgroup.mem_centralizer_singleton_iff.mp (hL.le hgL), mul_inv_cancel_right]
  have hC := ggRankOneIn_isComponentOf_centralizer hxH hL (hqs t ht htr)
  have hCn := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
    (f := (MulAut.conj n).toMonoidHom) (MulAut.conj n).injective).mpr hC
  rw [ggMap_conj_centralizer, ggHyperplane_map_conj ha] at hCn
  have hB := Subgroup.map_mono (f := (MulAut.conj n).toMonoidHom)
    (normalizer_ggRankOneIn (fun c hc d hd => hBs.comm hc hd) hBL t)
  have hnBs : Bs.map (MulAut.conj n).toMonoidHom = Bs := by
    ext b
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hn c).mp hc
    · intro hb
      refine ⟨n⁻¹ * b * n, ?_, ?_⟩
      · have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) b).mp hb
        simpa only [inv_inv, SetLike.mem_coe] using h
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
  rw [hnBs, Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj n).bijective] at hB
  have ha' : a = ggConjAut Bs hn := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    exact ha b
  refine ⟨hCn, hB, ?_, ?_, ?_⟩
  · rw [ggAutomizer_map_conj hn, ha']
    exact Subgroup.mem_map.mpr ⟨t, mem_ggAutomizer_ggRankOneIn ht htr.1, rfl⟩
  · rw [conj_pow, htr.1]
    group
  · intro h1
    apply htr.ne_one hpp
    calc t = a⁻¹ * (a * t * a⁻¹) * a := by group
      _ = 1 := by rw [h1]; group

theorem GGOriginalRankOneConjugate.eq
    (hpp : p.Prime) (hp : Odd p) (hBs : IsElemAbelian p Bs) (hx : x ∈ Bs)
    (hL : IsSubnormal L (Subgroup.centralizer ({x} : Set G)))
    (hBL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hqs : ∀ t ∈ ggAutomizer L Bs, GGIsReflection p t →
      CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn L Bs t))
    {r : MulAut ↥Bs} {S T : Subgroup G}
    (hS : GGOriginalRankOneConjugate p L H Bs r S)
    (hT : GGOriginalRankOneConjugate p L H Bs r T) : S = T := by
  obtain ⟨hSC, hBS, hrS, hr2, hr1⟩ := hS.component_data hpp hBs hx hL hBL hqs
  obtain ⟨hTC, -, hrT, -, -⟩ := hT.component_data hpp hBs hx hL hBL hqs
  exact eq_of_isComponentOf_of_mem_ggAutomizer hSC hTC
    (fun b hb h => eq_one_of_mul_self_eq_one_of_isElemAbelian hp hBs hb h)
    hBS hrS hrT hr2 hr1

theorem ggRankOneFrom_eq_of_conjugate
    (hpp : p.Prime) (hp : Odd p) (hBs : IsElemAbelian p Bs) (hx : x ∈ Bs)
    (hL : IsSubnormal L (Subgroup.centralizer ({x} : Set G)))
    (hBL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hqs : ∀ t ∈ ggAutomizer L Bs, GGIsReflection p t →
      CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn L Bs t))
    {r : MulAut ↥Bs} {S : Subgroup G} (hS : GGOriginalRankOneConjugate p L H Bs r S) :
    ggRankOneFrom p L H Bs r = S := by
  refine le_antisymm (iSup_le fun T => iSup_le fun hT => ?_) hS.le_ggRankOneFrom
  exact le_of_eq (hT.eq hpp hp hBs hx hL hBL hqs hS)

theorem ggRankOneFrom_eq_original
    (hpp : p.Prime) (hp : Odd p) (hBs : IsElemAbelian p Bs) (hx : x ∈ Bs)
    (hL : IsSubnormal L (Subgroup.centralizer ({x} : Set G)))
    (hBL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hqs : ∀ t ∈ ggAutomizer L Bs, GGIsReflection p t →
      CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn L Bs t))
    {r : MulAut ↥Bs} (hrL : r ∈ ggAutomizer L Bs) (hr : GGIsReflection p r) :
    ggRankOneFrom p L H Bs r = ggRankOneIn L Bs r := by
  apply ggRankOneFrom_eq_of_conjugate hpp hp hBs hx hL hBL hqs
  refine ⟨r, hrL, hr, 1, H.one_mem, Subgroup.one_mem _, 1, fun b => by simp, by simp, ?_⟩
  have h1 : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext z
    simp
  rw [h1, Subgroup.map_id]

theorem ggRankOneFrom_component_data
    (hpp : p.Prime) (hp : Odd p) (hBs : IsElemAbelian p Bs) (hx : x ∈ Bs)
    (hL : IsSubnormal L (Subgroup.centralizer ({x} : Set G)))
    (hBL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hqs : ∀ t ∈ ggAutomizer L Bs, GGIsReflection p t →
      CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn L Bs t))
    {r : MulAut ↥Bs} (hr : ∃ S, GGOriginalRankOneConjugate p L H Bs r S) :
    IsComponentOf (ggRankOneFrom p L H Bs r)
        (Subgroup.centralizer (ggHyperplane Bs r : Set G)) ∧
      Bs ≤ Subgroup.normalizer (ggRankOneFrom p L H Bs r : Set G) ∧
      r ∈ ggAutomizer (ggRankOneFrom p L H Bs r) Bs := by
  obtain ⟨S, hS⟩ := hr
  rw [ggRankOneFrom_eq_of_conjugate hpp hp hBs hx hL hBL hqs hS]
  obtain ⟨hC, hN, hA, -, -⟩ := hS.component_data hpp hBs hx hL hBL hqs
  exact ⟨hC, hN, hA⟩

end Components

end CFSG.StandardType

end
