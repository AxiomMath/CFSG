module

public import CFSG.LocalAnalysis.StandardType.GGExcKGSFTrSub

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

section Universal

namespace GGSFTr

variable {t : StatedLieTag} {n f p : ℕ} {M : GGKGModel t n f p} {G : Type} [Group G]
  {ψ : (ggU t n f).K →* G} {Bs : Subgroup G} (T : GGSFTr t n f p M ψ Bs)

private theorem toB_injective : Function.Injective T.toB := by
  intro b b' h
  apply T.toHom_injective
  have h1 : ((T.toB b : M.Bfull) : GGAutU t n f) =
      ((T.toB b' : M.Bfull) : GGAutU t n f) := congrArg Subtype.val h
  rwa [T.toB_val, T.toB_val] at h1

private theorem toB_ne_one {b : Bs} (hb : b ≠ 1) : T.toB b ≠ 1 := by
  intro h
  exact hb (T.toB_injective (by rw [h, map_one]))

private theorem hom_eq_coe_toB (b : Bs) :
    T.hom ⟨(b : G), T.bs_le b.2⟩ = ((T.toB b : M.Bfull) : GGAutU t n f) := by
  rw [T.toB_val b, T.toHom_apply b]

private theorem fwd_inf_centralizer_singleton_eq (b : Bs) :
    T.fwd (ψ.range ⊓ Subgroup.centralizer {(b : G)}) =
      (ggPsiU t n f).range ⊓
        Subgroup.centralizer {((T.toB b : M.Bfull) : GGAutU t n f)} := by
  rw [T.fwd_inf_centralizer_singleton (⟨b, T.bs_le b.2⟩ : T.N), T.hom_eq_coe_toB b]

theorem comp (h : GGClauseComp t n f p (ggPsiU t n f) M.Bfull M.S M.π M.coord) :
    GGClauseComp t n f p ψ Bs M.S M.π T.coord := by
  refine ⟨?_, ?_⟩
  ·
    intro b hb O hO hns
    have hb' : T.toB b ≠ 1 := T.toB_ne_one hb
    have hO' : IsCompOrbit M.S M.π
        (latPhi (ggU (absTag t) 6 f).D.roots p
          (Multiplicative.toAdd (M.coord (T.toB b)))) O := by
      simpa only [T.coord_apply b] using hO
    obtain ⟨Lb, hcompLb, hcentLb⟩ := h.1 (T.toB b) hb' O hO' hns
    have hLbInn : Lb ≤ (ggPsiU t n f).range := hcompLb.1.trans inf_le_left
    obtain ⟨L, hLψ, hfwd⟩ := T.exists_fwd_eq hLbInn
    have hLN : L ≤ T.N := hLψ.trans T.psi_le
    have hHN : (ψ.range ⊓ Subgroup.centralizer {(b : G)}) ≤ T.N :=
      inf_le_left.trans T.psi_le
    refine ⟨L, ?_, ?_⟩
    · have h3 : IsComponentOf (T.fwd L)
          (T.fwd (ψ.range ⊓ Subgroup.centralizer {(b : G)})) := by
        rw [hfwd, T.fwd_inf_centralizer_singleton_eq b]
        exact hcompLb
      exact (T.isComponentOf_fwd_iff hLN hHN).mp h3
    · intro c
      calc
        (c : G) ∈ Subgroup.centralizer (L : Set G) ↔
            T.hom ⟨(c : G), T.bs_le c.2⟩ ∈
              Subgroup.centralizer (T.fwd L : Set (GGAutU t n f)) :=
          T.mem_centralizer_fwd_iff hLN ⟨(c : G), T.bs_le c.2⟩
        _ ↔ ((T.toB c : M.Bfull) : GGAutU t n f) ∈
              Subgroup.centralizer (Lb : Set (GGAutU t n f)) := by
            rw [T.hom_eq_coe_toB c, hfwd]
        _ ↔ ∀ α ∈ O, latChar p
              (Multiplicative.toAdd (M.coord (T.toB c))) α = 0 :=
            hcentLb (T.toB c)
        _ ↔ ∀ α ∈ O, latChar p
              (Multiplicative.toAdd (T.coord c)) α = 0 := by
            rw [T.coord_apply c]
  ·
    intro b hb L hcomp
    have hLψ : L ≤ ψ.range := hcomp.1.trans inf_le_left
    have hLN : L ≤ T.N := hLψ.trans T.psi_le
    have hb' : T.toB b ≠ 1 := T.toB_ne_one hb
    have hHN : (ψ.range ⊓ Subgroup.centralizer {(b : G)}) ≤ T.N :=
      inf_le_left.trans T.psi_le
    have hcompLb : IsComponentOf (T.fwd L)
        ((ggPsiU t n f).range ⊓
          Subgroup.centralizer {((T.toB b : M.Bfull) : GGAutU t n f)}) := by
      have h3 : IsComponentOf (T.fwd L)
          (T.fwd (ψ.range ⊓ Subgroup.centralizer {(b : G)})) :=
        (T.isComponentOf_fwd_iff hLN hHN).mpr hcomp
      rwa [T.fwd_inf_centralizer_singleton_eq b] at h3
    obtain ⟨O, hO, hns, hcent, hnorm, hcoroot, hsingle⟩ :=
      h.2 (T.toB b) hb' (T.fwd L) hcompLb
    refine ⟨O, ?_, hns, ?_, ?_, ?_, ?_⟩
    · rw [T.coord_apply b]
      exact hO
    · intro c
      calc
        (c : G) ∈ Subgroup.centralizer (L : Set G) ↔
            T.hom ⟨(c : G), T.bs_le c.2⟩ ∈
              Subgroup.centralizer (T.fwd L : Set (GGAutU t n f)) :=
          T.mem_centralizer_fwd_iff hLN ⟨(c : G), T.bs_le c.2⟩
        _ ↔ ((T.toB c : M.Bfull) : GGAutU t n f) ∈
              Subgroup.centralizer (T.fwd L : Set (GGAutU t n f)) := by
            rw [T.hom_eq_coe_toB c]
        _ ↔ ∀ α ∈ O, latChar p
              (Multiplicative.toAdd (M.coord (T.toB c))) α = 0 :=
            hcent (T.toB c)
        _ ↔ ∀ α ∈ O, latChar p
              (Multiplicative.toAdd (T.coord c)) α = 0 := by
            rw [T.coord_apply c]
    · intro c hc
      apply (T.mem_normalizer_fwd_iff hLN ⟨c, T.bs_le hc⟩).mpr
      rw [T.hom_eq_coe_toB ⟨c, hc⟩, T.toB_val ⟨c, hc⟩]
      exact hnorm (T.toHom_mem ⟨c, hc⟩)
    · intro α hα hfix c hcoord
      apply (T.mem_fwd_iff ⟨(c : G), T.bs_le c.2⟩).mp
      rw [T.hom_eq_coe_toB c]
      exact hcoroot α hα hfix (T.toB c) (by rw [← T.coord_apply c]; exact hcoord)
    · rcases hsingle with hs | ⟨k, hk⟩
      · left
        rw [T.coord_apply b]
        exact hs
      · exact Or.inr ⟨k, T.lieModel_of_fwd hLN hk⟩

end GGSFTr

end Universal

end CFSG.StandardType
