module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreG1a
public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreG1b
public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreThetaModel

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.HallHigman Equiv Equiv.Perm CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem pSolv3_of_injective {X Y : Type} [Group X] [Group Y] [Finite Y] (g : X →* Y)
    (hg : Function.Injective g) (hY : IsPSolvable 3 Y) : IsPSolvable 3 X :=
  isPSolvable_of_mulEquiv (MonoidHom.ofInjective hg).symm (pSolv3_subgroup hY g.range)

theorem pSolv3_A' (h : FF84Sec4 b L B K b₁ b₂) (hA : A8Model L) :
    IsPSolvable 3 ↥(Cen (b₁ * b₂) ⊓ Cen b) := by
  obtain ⟨θ, hker, -, -, hc, hd⟩ := theta_model hA h
  set A' := Cen (b₁ * b₂) ⊓ Cen b with hA'
  have hAN : A' ≤ Nor L := fun a ha => h.hyp.hLN (Subgroup.mem_inf.1 ha).2
  set f : ↥A' →* Perm (Fin 8) := θ.comp (Subgroup.inclusion hAN) with hf
  have hb₁L : b₁ ∈ L := (Subgroup.mem_inf.1 h.hb₁).2
  have hb₂L : b₂ ∈ L := (Subgroup.mem_inf.1 h.hb₂).2
  have hrange : f.range ≤ Subgroup.centralizer ({sig} : Set (Perm (Fin 8))) := by
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hac : a.1 * (b₁ * b₂) = (b₁ * b₂) * a.1 :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 a.2).1
    have hcomm : (⟨a.1, hAN a.2⟩ : ↥(Nor L)) *
        ((⟨b₁, Subgroup.le_normalizer hb₁L⟩ : ↥(Nor L)) * ⟨b₂, Subgroup.le_normalizer hb₂L⟩) =
        ((⟨b₁, Subgroup.le_normalizer hb₁L⟩ : ↥(Nor L)) * ⟨b₂, Subgroup.le_normalizer hb₂L⟩) *
          ⟨a.1, hAN a.2⟩ := Subtype.ext hac
    have := congrArg θ hcomm
    simp only [map_mul, hc, hd] at this
    exact this
  have hsolv : Group.IsSolvable ↥f.range := by
    haveI := solvable_cent_sig
    exact solvable_of_solvable_injective (Subgroup.inclusion_injective hrange)
  have hker' : ∀ x : ↥f.ker, x.1.1 ∈ CenS L := fun x =>
    (hker ⟨x.1.1, hAN x.1.2⟩).1 (MonoidHom.mem_ker.1 x.2)
  let g : ↥f.ker →* ↥(Cen b ⊓ CenS L) :=
    { toFun := fun x => ⟨x.1.1, Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 x.1.2).2, hker' x⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hg : Function.Injective g := by
    intro x y hxy
    have h1 : ((g x : ↥(Cen b ⊓ CenS L)) : G) = ((g y : ↥(Cen b ⊓ CenS L)) : G) :=
      congrArg Subtype.val hxy
    apply Subtype.ext
    apply Subtype.ext
    exact h1
  have hkerP : IsPSolvable 3 ↥f.ker := pSolv3_of_injective g hg (pSolv3_ZZ h.hyp)
  have hQ : IsPSolvable 3 (↥A' ⧸ f.ker) :=
    isPSolvable_of_mulEquiv (QuotientGroup.quotientKerEquivRange f).symm (pSolv3_of_solvable hsolv)
  exact pSolv3_of_normal f.ker hkerP hQ

theorem pSolv3_G1 (h : FF84Sec4 b L B K b₁ b₂) (hA : A8Model L) :
    IsPSolvable 3 ↥(Cen (b * b₁) ⊓ Cen b₂) := by
  obtain ⟨n, hn, hnb, hnb₁, hnb₂⟩ := h.mono.2.2.2.2.2
  have hmem : ∀ a ∈ Cen (b * b₁) ⊓ Cen b₂,
      n * a * n⁻¹ ∈ Cen (b₁ * b₂) ⊓ Cen b := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := Subgroup.mem_inf.1 ha
    have h1 : a * (b * b₁) = (b * b₁) * a := Subgroup.mem_centralizer_singleton_iff.1 ha1
    have h2 : a * b₂ = b₂ * a := Subgroup.mem_centralizer_singleton_iff.1 ha2
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    · have e : n * (b * b₁) * n⁻¹ = b₁ * b₂ := by
        calc n * (b * b₁) * n⁻¹ = (n * b * n⁻¹) * (n * b₁ * n⁻¹) := by group
          _ = b₁ * b₂ := by rw [hnb, hnb₁]
      calc n * a * n⁻¹ * (b₁ * b₂) = n * a * n⁻¹ * (n * (b * b₁) * n⁻¹) := by rw [e]
        _ = n * (a * (b * b₁)) * n⁻¹ := by group
        _ = n * ((b * b₁) * a) * n⁻¹ := by rw [h1]
        _ = (n * (b * b₁) * n⁻¹) * (n * a * n⁻¹) := by group
        _ = (b₁ * b₂) * (n * a * n⁻¹) := by rw [e]
    · calc n * a * n⁻¹ * b = n * a * n⁻¹ * (n * b₂ * n⁻¹) := by rw [hnb₂]
        _ = n * (a * b₂) * n⁻¹ := by group
        _ = n * (b₂ * a) * n⁻¹ := by rw [h2]
        _ = (n * b₂ * n⁻¹) * (n * a * n⁻¹) := by group
        _ = b * (n * a * n⁻¹) := by rw [hnb₂]
  set A' := Cen (b₁ * b₂) ⊓ Cen b with hA'
  have hsub : Cen (b * b₁) ⊓ Cen b₂ ≤ A'.map (MulAut.conj n⁻¹).toMonoidHom := by
    intro a ha
    refine Subgroup.mem_map.2 ⟨n * a * n⁻¹, hmem a ha, ?_⟩
    simp [MulAut.conj_apply]
    group
  exact isPSolvable_of_le
    (isPSolvable_map (MulAut.conj n⁻¹).toMonoidHom (pSolv3_A' h hA)) hsub

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
