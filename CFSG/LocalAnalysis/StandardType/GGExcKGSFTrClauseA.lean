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

theorem clauseA (h : GGClauseA t n f p (ggPsiU t n f) M.Bfull M.S M.π M.coord) :
    GGClauseA t n f p ψ Bs M.S M.π T.coord := by
  intro b hb L hcomp
  have hLψ : L ≤ ψ.range := hcomp.1.trans inf_le_left
  have hLN : L ≤ T.N := hLψ.trans T.psi_le
  have hHN : (ψ.range ⊓ Subgroup.centralizer {(b : G)}) ≤ T.N :=
    inf_le_left.trans T.psi_le
  have hb' : T.toB b ≠ 1 := T.toB_ne_one hb
  have hcompLb : IsComponentOf (T.fwd L)
      ((ggPsiU t n f).range ⊓
        Subgroup.centralizer {((T.toB b : M.Bfull) : GGAutU t n f)}) := by
    have h3 : IsComponentOf (T.fwd L)
        (T.fwd (ψ.range ⊓ Subgroup.centralizer {(b : G)})) :=
      (T.isComponentOf_fwd_iff hLN hHN).mpr hcomp
    rwa [T.fwd_inf_centralizer_singleton_eq b] at h3
  obtain ⟨O, hO, hcent, hcoroot⟩ := h (T.toB b) hb' (T.fwd L) hcompLb
  refine ⟨O, ?_, ?_, ?_⟩
  · simpa only [T.coord_apply b] using hO
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
    apply (T.mem_fwd_iff ⟨(c : G), T.bs_le c.2⟩).mp
    rw [T.hom_eq_coe_toB c]
    exact hcoroot (T.toB c) (by rw [← T.coord_apply c]; exact hc)

theorem clauseAU (h : GGClauseAU t n f p (ggPsiU t n f) M.Bfull M.S M.π M.coord) :
    GGClauseAU t n f p ψ Bs M.S M.π T.coord := by
  intro U hUB hUne K hcomp
  have hUN : U ≤ T.N := hUB.trans T.bs_le
  have hKψ : K ≤ ψ.range := hcomp.1.trans inf_le_left
  have hKN : K ≤ T.N := hKψ.trans T.psi_le
  have hHN : (ψ.range ⊓ Subgroup.centralizer (U : Set G)) ≤ T.N :=
    inf_le_left.trans T.psi_le
  have hU'le : T.fwd U ≤ M.Bfull := by
    rintro a ⟨x, hxU, rfl⟩
    have hx' : (x : G) ∈ Bs := hUB hxU
    have hx_eq : x = (⟨(x : G), T.bs_le hx'⟩ : T.N) := Subtype.ext rfl
    rw [hx_eq, T.hom_eq_coe_toB ⟨(x : G), hx'⟩]
    exact (T.toB ⟨(x : G), hx'⟩).2
  have hU'ne : T.fwd U ≠ ⊥ := by
    intro hbot
    apply hUne
    rw [Subgroup.eq_bot_iff_forall]
    intro u hu
    have huN : u ∈ T.N := hUN hu
    have hmem : T.hom ⟨u, huN⟩ ∈ T.fwd U := (T.mem_fwd_iff ⟨u, huN⟩).2 hu
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : (⟨u, huN⟩ : T.N) = 1 := T.hom_inj (by rw [hmem, map_one])
    exact congrArg Subtype.val h1
  have hcomp' : IsComponentOf (T.fwd K)
      ((ggPsiU t n f).range ⊓
        Subgroup.centralizer (T.fwd U : Set (GGAutU t n f))) := by
    have h3 : IsComponentOf (T.fwd K)
        (T.fwd (ψ.range ⊓ Subgroup.centralizer (U : Set G))) :=
      (T.isComponentOf_fwd_iff hKN hHN).mpr hcomp
    rwa [T.fwd_inf_centralizer hUN] at h3
  obtain ⟨O, hO, hcent⟩ := h (T.fwd U) hU'le hU'ne (T.fwd K) hcomp'
  have hR : {α | α ∈ (ggU (absTag t) 6 f).D.roots ∧
        ∀ u : Bs, (u : G) ∈ U →
          latChar p (Multiplicative.toAdd (T.coord u)) α = 0} =
      {α | α ∈ (ggU (absTag t) 6 f).D.roots ∧
        ∀ u : M.Bfull, (u : GGAutU t n f) ∈ T.fwd U →
          latChar p (Multiplicative.toAdd (M.coord u)) α = 0} := by
    ext α
    constructor
    · intro hα
      refine ⟨hα.1, ?_⟩
      intro u hu
      obtain ⟨x, hxU, hxu⟩ := hu
      have hx' : (x : G) ∈ Bs := hUB hxU
      have hx_eq : x = (⟨(x : G), T.bs_le hx'⟩ : T.N) := Subtype.ext rfl
      have hu_eq : u = T.toB ⟨(x : G), hx'⟩ := by
        apply Subtype.ext
        rw [← hxu]
        exact congrArg T.hom hx_eq
      have hcoord : M.coord u = T.coord ⟨(x : G), hx'⟩ := by
        rw [hu_eq, T.coord_apply]
      rw [hcoord]
      exact hα.2 ⟨(x : G), hx'⟩ hxU
    · intro hα
      refine ⟨hα.1, ?_⟩
      intro u hu
      have hmem : ((T.toB u : M.Bfull) : GGAutU t n f) ∈ T.fwd U := by
        have h1 := (T.mem_fwd_iff ⟨(u : G), T.bs_le u.2⟩).2 hu
        rwa [T.hom_eq_coe_toB u] at h1
      rw [T.coord_apply u]
      exact hα.2 (T.toB u) hmem
  refine ⟨O, ?_, ?_⟩
  · rw [hR]
    exact hO
  · intro b' hb'
    have hb'm : ∀ α ∈ O,
        latChar p (Multiplicative.toAdd (M.coord (T.toB b'))) α = 0 := by
      intro α hα
      rw [← T.coord_apply b']
      exact hb' α hα
    have hmem : ((T.toB b' : M.Bfull) : GGAutU t n f) ∈
        Subgroup.centralizer (T.fwd K : Set (GGAutU t n f)) := hcent (T.toB b') hb'm
    exact (T.mem_centralizer_fwd_iff hKN ⟨(b' : G), T.bs_le b'.2⟩).mpr (by
      rw [T.hom_eq_coe_toB b']
      exact hmem)

end GGSFTr

end Universal

end CFSG.StandardType
