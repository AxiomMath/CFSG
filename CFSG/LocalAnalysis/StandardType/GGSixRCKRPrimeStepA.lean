module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeDefs
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompNormal

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1
open CFSG.Open (StatedLieTag)

theorem le_normalizer_and_exists_isComponentOf_of_plane
    {X : Type} [Group X] [Finite X] {p : ℕ} {G₀ A B₁ D J K : Subgroup X} {e : X}
    (hp : p.Prime) (hAelem : IsElemAbelian p A) (hB1A : B₁ ≤ A) (hDB1 : D ≤ B₁)
    (hDcard : Nat.card D = p ^ 2) (hAnormG0 : A ≤ Subgroup.normalizer (G₀ : Set X))
    (hB1normJ : B₁ ≤ Subgroup.normalizer (J : Set X))
    (hJcompD : IsComponentOf J (Subgroup.centralizer (D : Set X) ⊓ G₀))
    (heD : e ∈ D) (he1 : e ≠ 1)
    (hKcomp : IsComponentOf K (G₀ ⊓ Subgroup.centralizer {e})) (hJK : J ≤ K) :
    B₁ ≤ Subgroup.normalizer (K : Set X) ∧ ∃ d ∈ D, d ∉ Subgroup.zpowers e ∧
      IsComponentOf J (K ⊓ Subgroup.centralizer {d}) := by
  have hJqs : Assembly.IsQuasisimple ↥J := hJcompD.2.2
  have hAcomm : IsMulCommutative A := hAelem.1
  have hApow : ∀ x ∈ A, x ^ p = 1 := hAelem.2
  have heA : e ∈ A := hB1A (hDB1 heD)
  refine ⟨?_, ?_⟩
  ·
    intro b hb
    have hbA : b ∈ A := hB1A hb
    have hbG0 : b ∈ Subgroup.normalizer (G₀ : Set X) := hAnormG0 hbA
    have hbe : b * e * b⁻¹ = e := by
      have hcomm : b * e = e * b := congrArg Subtype.val
        (hAcomm.is_comm.comm (⟨b, hbA⟩ : A) (⟨e, heA⟩ : A))
      rw [hcomm]; group
    have hbG0' : G₀.map (MulAut.conj b).toMonoidHom = G₀ := by
      simpa using (Subgroup.mem_normalizer_iff_map_conj_eq.mp hbG0)
    have hbCe : (Subgroup.centralizer ({e} : Set X)).map (MulAut.conj b).toMonoidHom =
        Subgroup.centralizer ({e} : Set X) :=
      (CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton b e).trans (by rw [hbe])
    have hHmap : (G₀ ⊓ Subgroup.centralizer ({e} : Set X)).map (MulAut.conj b).toMonoidHom =
        G₀ ⊓ Subgroup.centralizer ({e} : Set X) := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj b).injective, hbG0', hbCe]
    have hKb : IsComponentOf (K.map (MulAut.conj b).toMonoidHom)
        (G₀ ⊓ Subgroup.centralizer ({e} : Set X)) := by
      have h1 := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hKcomp b
      rwa [hHmap] at h1
    have hbJ' : J.map (MulAut.conj b).toMonoidHom = J :=
      CFSG.LocalAnalysis.ComponentInitial.conjSub_eq_of_mem_normalizer (hB1normJ hb)
    have hJKb : J ≤ K.map (MulAut.conj b).toMonoidHom := by
      rw [← hbJ']
      exact Subgroup.map_mono hJK
    have hKeq : K.map (MulAut.conj b).toMonoidHom = K :=
      CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_of_le hJqs hKb hKcomp hJKb hJK
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hKeq
  ·
    have hepow : e ^ p = 1 := hApow e heA
    haveI : Fact p.Prime := ⟨hp⟩
    have horder_e : orderOf e = p := orderOf_eq_prime hepow he1
    have hcard_zp : Nat.card (Subgroup.zpowers e) = p := by
      rw [Nat.card_zpowers, horder_e]
    obtain ⟨d, hdD, hdnot⟩ : ∃ d ∈ D, d ∉ Subgroup.zpowers e := by
      by_contra hc
      simp only [not_exists, not_and, not_not] at hc
      have hle : D ≤ Subgroup.zpowers e := hc
      have hcardle : Nat.card D ≤ Nat.card (Subgroup.zpowers e) := Subgroup.card_le_of_le hle
      rw [hDcard, hcard_zp] at hcardle
      have hlt : p < p ^ 2 := by
        rw [pow_two]
        exact lt_mul_self hp.one_lt
      exact absurd hcardle (not_le.mpr hlt)
    have hd1 : d ≠ 1 := by
      intro hd1
      apply hdnot
      rw [hd1]
      exact Subgroup.one_mem _
    have hDgen : Subgroup.closure ({e, d} : Set X) = D :=
      ggClosure_pair_eq hp hDcard heD hdD he1 hepow hdnot
    have hKleG0 : K ≤ G₀ := hKcomp.1.trans inf_le_left
    have hKleCe : K ≤ Subgroup.centralizer ({e} : Set X) := hKcomp.1.trans inf_le_right
    have hJleCD : J ≤ Subgroup.centralizer (D : Set X) := hJcompD.1.trans inf_le_left
    refine ⟨d, hdD, hdnot, ?_⟩
    refine hJcompD.of_le_of_le ?_ ?_
    · exact le_inf hJK (hJleCD.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hdD)))
    · intro x hx
      rw [Subgroup.mem_inf] at hx ⊢
      obtain ⟨hxK, hxd⟩ := hx
      refine ⟨?_, hKleG0 hxK⟩
      have hxe : x ∈ Subgroup.centralizer ({e} : Set X) := hKleCe hxK
      have hxC : x ∈ Subgroup.centralizer (Subgroup.closure ({e, d} : Set X) : Set X) := by
        rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with heq | heq
        · rw [heq]
          exact (Subgroup.mem_centralizer_iff.mp hxe) e rfl
        · rw [heq]
          exact (Subgroup.mem_centralizer_iff.mp hxd) d rfl
      rwa [hDgen] at hxC


theorem rckRP_stepA
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ} {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X}
    (h : RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e) :
    B₁ ≤ Subgroup.normalizer (K : Set X) ∧ ∃ d ∈ D, d ∉ Subgroup.zpowers e ∧
      IsComponentOf J (K ⊓ Subgroup.centralizer {d}) := by
  unfold RCKRPConfig at h
  rcases h with ⟨_, _, hp, _, hAelem, hB1A, hDB1, hDcard, hAnormG0, _,
    hB1normJ, _, _, _, _, _, _, _, hJcompD, _, _, _, _, _, _, _, _, _, heD, he1,
    hKcomp, hJK, _⟩
  exact le_normalizer_and_exists_isComponentOf_of_plane hp hAelem hB1A hDB1 hDcard
    hAnormG0 hB1normJ hJcompD heD he1 hKcomp hJK

end CFSG.StandardType.RCKRP
