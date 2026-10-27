module

public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch22Defs
import CFSG.Foundations.KCoreOpen
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.GroupTheory.SteinbergBKOddNoncyclicRankTwo
import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

theorem pRank_map_subtype {Q : Type} [Group Q] [Finite Q] {H : Subgroup Q} (X : Subgroup ↥H)
    (p : ℕ) : CFSG.Open.pRank p (X.map H.subtype) = CFSG.Open.pRank p X :=
  CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective p H.subtype_injective X

theorem two_le_pRank_of_le_map {K Y : Type} [Group K] [Group Y] [Finite K] [Finite Y]
    (φ : K →* Y) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup K} {Xb : Subgroup Y}
    (hle : Xb ≤ X.map φ) (h : 2 ≤ CFSG.Open.pRank p Xb) : 2 ≤ CFSG.Open.pRank p X := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hEXb, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt Xb
  let W : Subgroup K := X ⊓ E.comap φ
  let φW : ↥W →* ↥E := (φ.comp W.subtype).codRestrict E fun w => (Subgroup.mem_inf.1 w.2).2
  have hφW : Function.Surjective φW := by
    rintro ⟨e, he⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 (hle (hEXb he))
    exact ⟨⟨x, Subgroup.mem_inf.2 ⟨hx, he⟩⟩, rfl⟩
  obtain ⟨S⟩ : Nonempty (Sylow p ↥W) := inferInstance
  have hpE : IsPGroup p ↥E := IsPGroup.of_card hcard
  have hSE : (S : Subgroup ↥W).map φW = ⊤ := by
    rw [← Sylow.coe_mapSurjective hφW]
    exact ((S.mapSurjective hφW).is_maximal' (hpE.to_subgroup ⊤) le_top).symm
  have hg : Function.Surjective (φW.comp (S : Subgroup ↥W).subtype) := by
    intro e
    have he : e ∈ (S : Subgroup ↥W).map φW := by
      rw [hSE]
      exact Subgroup.mem_top e
    obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.1 he
    exact ⟨⟨s, hs⟩, hse⟩
  have hnc : ¬ IsCyclic ↥(S : Subgroup ↥W) := by
    intro hc
    have hcE : IsCyclic ↥E := isCyclic_of_surjective _ hg
    have hexp : Monoid.exponent ↥E ∣ p :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hE.2 x x.2)
    rw [IsCyclic.exponent_eq_card, hcard] at hexp
    have h1 : p ^ 2 ≤ p :=
      (Nat.pow_le_pow_right hp.pos h).trans (Nat.le_of_dvd hp.pos hexp)
    have := hp.two_le
    nlinarith
  obtain ⟨B, hB, hBc⟩ := CFSG.GroupTheory.SteinbergBK.odd_noncyclic_pgroup_rank_two
    (hp.odd_of_ne_two hp2) S.isPGroup' hnc
  have := hB
  refine CFSG.SectionRank.le_pRank_of_injective hp.one_lt (fun a b => mul_comm' a b)
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (IsElementaryAbelian.exponent_dvd_p p ↥B)) hBc
    (W.subtype.comp ((S : Subgroup ↥W).subtype.comp B.subtype))
    (Subtype.val_injective.comp (Subtype.val_injective.comp Subtype.val_injective)) ?_
  intro y hy
  obtain ⟨b, rfl⟩ := MonoidHom.mem_range.1 hy
  exact (Subgroup.mem_inf.1 ((b : ↥(S : Subgroup ↥W)) : ↥W).2).1

private theorem commutator_top_eq_top {Z : Type} [Group Z] [IsSimpleGroup Z]
    (hnab : ∃ a b : Z, a * b ≠ b * a) : ⁅(⊤ : Subgroup Z), (⊤ : Subgroup Z)⁆ = ⊤ := by
  have := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1.1
  exact Subgroup.commutator_eq_self

theorem three_lt_pRank_perfectCore_of_section (h22 : Asch2_2Simple)
    {Q : Type} [Group Q] [Finite Q] {H X : Subgroup Q} (hK : CFSG.Open.IsKGroup ↥H) (hXH : X ≤ H)
    {Z : Type} [Group Z] [Finite Z] [IsSimpleGroup Z] (hnab : ∃ a b : Z, a * b ≠ b * a)
    (ψ : ↥X →* Z) (hψ : Function.Surjective ψ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrk : 3 < CFSG.Open.pRank p (⊤ : Subgroup Z))
    (hON : p = 3 → ¬ Nonempty (Z ≃* CFSG.Blueprint.NativeSporadic.ON)) :
    3 < CFSG.Open.pRank p (perfectCore H) := by
  by_contra hle
  rw [not_lt] at hle
  have hXH' : perfectCore X ≤ perfectCore H := perfectCore_mono hXH
  have hψ' : (perfectCore (⊤ : Subgroup ↥X)).map ψ = ⊤ := by
    rw [map_perfectCore, Subgroup.map_top_of_surjective ψ hψ,
      perfectCore_eq_self_of_perfect (commutator_top_eq_top hnab)]
  have hX : (perfectCore (⊤ : Subgroup ↥X)).map X.subtype = perfectCore X := by
    rw [map_perfectCore, Subgroup.map_top, Subgroup.range_subtype]
  let H₀ : Subgroup ↥(perfectCore H) := (perfectCore X).subgroupOf (perfectCore H)
  let f₀ : ↥H₀ →* Z := ψ.comp (((perfectCore H).subtype.comp H₀.subtype).codRestrict X
    fun h => perfectCore_le X (Subgroup.mem_subgroupOf.1 h.2))
  have hf₀ : Function.Surjective f₀ := by
    intro z
    have hz : z ∈ (perfectCore (⊤ : Subgroup ↥X)).map ψ := by
      rw [hψ']
      exact Subgroup.mem_top z
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hz
    have hyX : (y : Q) ∈ perfectCore X := by
      rw [← hX]
      exact Subgroup.mem_map_of_mem X.subtype hy
    exact ⟨⟨⟨y, hXH' hyX⟩, Subgroup.mem_subgroupOf.2 hyX⟩, rfl⟩
  let e : ↥H₀ ⧸ f₀.ker ≃* Z := QuotientGroup.quotientKerEquivOfSurjective f₀ hf₀
  have : IsSimpleGroup (↥H₀ ⧸ f₀.ker) := e.isSimpleGroup
  have hnab₀ : ∃ a b : ↥H₀ ⧸ f₀.ker, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    simpa using congrArg e h
  have hrk₀ : CFSG.Open.pRank p (⊤ : Subgroup ↥(perfectCore H)) ≤ 3 := by
    rw [← pRank_map_subtype, Subgroup.map_top, Subgroup.range_subtype]
    exact hle
  have hZe : CFSG.Open.pRank p (⊤ : Subgroup (↥H₀ ⧸ f₀.ker)) =
      CFSG.Open.pRank p (⊤ : Subgroup Z) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e
  rcases h22 ↥(perfectCore H) (hK.of_le (perfectCore_le H)) p hp hp2 hrk₀ H₀ f₀.ker this
      hnab₀ with h | ⟨hp3, ⟨e'⟩⟩
  · omega
  · exact hON hp3 ⟨e.symm.trans e'⟩

end CFSG.LocalAnalysis.WeakClosure81

end
