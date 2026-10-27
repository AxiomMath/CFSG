module

public import CFSG.Quasithin.Background.RonanE211Six
public import CFSG.Quasithin.Vol2.E2TenSevenPair
public import CFSG.Quasithin.Vol2.E2NinePullback
import CFSG.Mathlib.GroupTheory.PermCommute
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.RonanE211

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.E2 CFSG.Quasithin.E2.Pair B6
  CFSG.Quasithin.Ch3E213M CFSG.Quasithin.Ch3E213M.P6E CFSG.QuasithinUnique.Borel252.A6

variable {G : Type} [Group G] [Finite G] {X T M V : Subgroup G} {g : G}

theorem center_six_of_pair (h : Pair X T M V g) [((PP M V X g).subgroupOf X).Normal]
    (hKG : KGI22One) (hOdd : OddCoverExact P6) (e : StarQuot M X ≃* P6)
    (hSyl : IsSylowTwoOf (star M X T) ⊤)
    (hVT : star M X V ≤ Subgroup.centralizer (star M X T : Set (StarQuot M X))) :
    Subgroup.center (Xbar M V X g) = Jbar M V X g ∧
      (∀ z ∈ Subgroup.center (Xbar M V X g), z * z = 1) ∧ pCoreOf 2 X = kerIn M X := by
  have hJn := h.normal_Jbar
  have hJc := h.Jbar_le_center
  have hPJ : (PP M V X g).subgroupOf X ≤ (kerIn M X).subgroupOf X :=
    Subgroup.subgroupOf_mono X h.P_le_J
  let ρ : Xbar M V X g →* P6 := QuotientGroup.lift ((PP M V X g).subgroupOf X)
    (e.toMonoidHom.comp (QuotientGroup.mk' ((kerIn M X).subgroupOf X))) (fun x hx => by
      have : QuotientGroup.mk' ((kerIn M X).subgroupOf X) x = 1 :=
        (QuotientGroup.eq_one_iff x).2 (hPJ hx)
      exact MonoidHom.mem_ker.2 (by rw [MonoidHom.comp_apply, this, map_one]))
  have hρmk : ∀ x : ↥X, ρ (piX M V X g x) = e (QuotientGroup.mk' ((kerIn M X).subgroupOf X) x) :=
    fun x => rfl
  have hρs : Function.Surjective ρ := by
    intro y
    obtain ⟨s, rfl⟩ := e.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ((kerIn M X).subgroupOf X) s
    exact ⟨piX M V X g x, hρmk x⟩
  have hker : ∀ x : ↥X, ρ (piX M V X g x) = 1 ↔ x ∈ (kerIn M X).subgroupOf X := by
    intro x
    rw [hρmk, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hρk : ρ.ker = Jbar M V X g := by
    ext z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ((PP M V X g).subgroupOf X) z
    rw [MonoidHom.mem_ker, hker]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have h1 : y⁻¹ * x ∈ (PP M V X g).subgroupOf X := QuotientGroup.eq.1 hyx
      have : x = y * (y⁻¹ * x) := by group
      rw [this]
      exact Subgroup.mul_mem _ hy (hPJ h1)
  set T₀ : Subgroup (Xbar M V X g) := (T.subgroupOf X).map (piX M V X g) ⊔ Jbar M V X g with hT₀
  have hVJ : Vbar M V X g ⊓ Jbar M V X g = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨hv, hj⟩
    obtain ⟨⟨v, hvX⟩, hvV, rfl⟩ := hv
    have h1 : ρ (piX M V X g ⟨v, hvX⟩) = 1 := by
      have : piX M V X g ⟨v, hvX⟩ ∈ ρ.ker := hρk ▸ hj
      exact this
    have h2 : v ∈ kerIn M X := Subgroup.mem_subgroupOf.1 ((hker _).1 h1)
    have h3 : v ∈ PP M V X g := Subgroup.mem_sup_left ⟨h2, Subgroup.mem_subgroupOf.1 hvV⟩
    have h4 : (⟨v, hvX⟩ : ↥X) ∈ (PP M V X g).subgroupOf X := Subgroup.mem_subgroupOf.2 h3
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff _).2 h4
  have hVT' : Vbar M V X g ≤ T₀ := by
    refine le_trans ?_ le_sup_left
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono X h.le_T)
  have hTV' : T₀ ≤ Subgroup.normalizer (Vbar M V X g : Set (Xbar M V X g)) := by
    refine sup_le ?_ (hJc.trans (Subgroup.center_le_normalizer _))
    have h1 : (T.subgroupOf X) ≤ Subgroup.normalizer ((V.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
      intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro x
      exact Subgroup.mem_normalizer_iff.1 (h.normal_T (Subgroup.mem_subgroupOf.1 ht)) (x : G)
    exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map _)
  have hmap : T₀.map ρ = (star M X T).map e.toMonoidHom := by
    have hcomp : ρ.comp (piX M V X g) =
        e.toMonoidHom.comp (QuotientGroup.mk' ((kerIn M X).subgroupOf X)) := MonoidHom.ext hρmk
    rw [hT₀, Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).2 (le_of_eq hρk.symm), sup_bot_eq,
      Subgroup.map_map, hcomp, ← Subgroup.map_map]
    rfl
  have hSyl' : IsSylowTwoOf (T₀.map ρ) ⊤ := by
    rw [hmap]
    exact isSylowTwoOf_map_mulEquiv e hSyl
  have hVc : ∀ v ∈ Vbar M V X g, ∀ t ∈ T₀, ρ v * ρ t = ρ t * ρ v := by
    intro v hv t ht
    obtain ⟨⟨v₀, hv₀X⟩, hv₀V, rfl⟩ := hv
    have hρt : ρ t ∈ (star M X T).map e.toMonoidHom := hmap ▸ Subgroup.mem_map_of_mem ρ ht
    obtain ⟨s, hs, hst⟩ := hρt
    have hsv : QuotientGroup.mk' ((kerIn M X).subgroupOf X) ⟨v₀, hv₀X⟩ ∈ star M X V :=
      ⟨⟨v₀, hv₀X⟩, hv₀V, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.1 (hVT hsv) s hs
    rw [hρmk, ← hst]
    show e _ * e s = e s * e _
    rw [← map_mul, ← map_mul]
    exact congrArg e hcomm.symm
  have hsq := sq_eq_one_of_perm_six hKG hOdd (Jbar M V X g) hJc ρ hρs hρk (Vbar M V X g) T₀
    h.Vbar_sq hVJ hVT' hTV' hSyl' hVc h.top_eq_Vbar_sup_conj.symm
  have hZ : Subgroup.center (Xbar M V X g) = Jbar M V X g := by
    refine le_antisymm (fun z hz => ?_) hJc
    have : ρ z ∈ Subgroup.center P6 := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨w, rfl⟩ := hρs y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz w]
    have h1 : ρ z = 1 :=
      CFSG.perm_eq_one_of_forall_commute (by simp) fun y =>
        (Subgroup.mem_center_iff.1 this y).symm
    rw [← hρk]
    exact h1
  have hsq' : ∀ z ∈ Subgroup.center (Xbar M V X g), z * z = 1 := fun z hz => hsq z (hZ ▸ hz)
  refine ⟨hZ, hsq', le_antisymm h.pCoreOf_le_kerIn ?_⟩
  have hP2 : IsPGroup 2 (PP M V X g) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le h.P_le_pCoreOf
  have hJ2 : IsPGroup 2 (kerIn M X) := by
    intro j
    have hjX : (j : G) ∈ X := kerIn_le.trans h.le_X j.2
    have hjc : piX M V X g (⟨j, hjX⟩ : X) ∈ Subgroup.center (Xbar M V X g) := by
      rw [hZ]
      exact ⟨⟨j, hjX⟩, Subgroup.mem_subgroupOf.2 j.2, rfl⟩
    have hjj := hsq' _ hjc
    rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hjj
    obtain ⟨k, hk⟩ := hP2 ⟨_, hjj⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hk' := congrArg Subtype.val hk
    simp only [SubmonoidClass.coe_pow, Subgroup.coe_mul, OneMemClass.coe_one] at hk'
    rw [SubmonoidClass.coe_pow, pow_succ', pow_mul, pow_two, OneMemClass.coe_one]
    exact hk'
  exact h.le_pCoreOf_of_le_kerIn hJ2 le_rfl

end CFSG.Quasithin.RonanE211
