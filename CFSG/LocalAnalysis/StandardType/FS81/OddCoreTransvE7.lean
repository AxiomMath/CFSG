module

public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreTransvOrth
public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreE7Irr

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

variable {G : Type} [Group G] [Finite G]

theorem Basis3.fix_of_mem_realized {n : ℕ} (B : Basis3 G (n + 1)) {b₀ : G} (hb0 : B.b 0 = b₀)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)}
    (hA : A ∈ B.realized (Subgroup.centralizer ({b₀} : Set G))) :
    A *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  obtain ⟨φ, ⟨g, hgC, -, hg⟩, rfl⟩ := (B.mem_realized_iff _ _).mp hA
  have hfix : φ (B.bS 0) = B.bS 0 := by
    apply Subtype.ext
    rw [hg]
    show g * B.b 0 * g⁻¹ = B.b 0
    rw [hb0, ← Subgroup.mem_centralizer_iff.mp hgC b₀ (Set.mem_singleton b₀)]
    group
  rw [← B.coords_bS 0, ← B.coords_apply, hfix]

theorem card_xg_fixE0 {n : ℕ} (B : Basis3 G (n + 1)) {b₀ : G} (hb0 : B.b 0 = b₀) :
    Nat.card ↥((ggAutomizer ⊤ B.span).map B.glHom ⊓ fixE0 n) =
      Nat.card ↥(B.realized (Subgroup.centralizer ({b₀} : Set G))) := by
  let f : ↥((ggAutomizer ⊤ B.span).map B.glHom ⊓ fixE0 n) →
      ↥(B.realized (Subgroup.centralizer ({b₀} : Set G))) := fun x =>
    ⟨((x : GL (Fin (n + 1)) (ZMod 3)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 3)),
      B.fix_mem_realized hb0 x.2.1 (mem_fixE0.mp x.2.2)⟩
  refine Nat.card_eq_of_bijective f ⟨fun x y hxy =>
    Subtype.ext (Units.ext (congrArg Subtype.val hxy)), ?_⟩
  rintro ⟨A, hA⟩
  obtain ⟨x, hx, hxA⟩ := B.exists_xg_of_realized _ hA
  refine ⟨⟨x, hx, mem_fixE0.mpr ?_⟩, Subtype.ext hxA⟩
  rw [hxA]
  exact B.fix_of_mem_realized hb0 hA

theorem transvAll_E7 {b₀ : G} {K E : Subgroup G} (B : Basis3 G (7 + 1))
    (hB : Adapted B b₀ K E) (hord : orderOf b₀ = 3)
    (hdisj : Disjoint (Subgroup.zpowers b₀) (E ⊓ K))
    (hKn : ∀ g ∈ Subgroup.centralizer ({b₀} : Set G), ∀ y ∈ K, g * y * g⁻¹ ∈ K)
    (hloc : LocalE7 B b₀) (hfus : Fus42 B b₀) (hodd : ¬ OddCoreTrivial E) :
    TransvAll b₀ K E := by
  obtain ⟨hcardC, -, hH1⟩ := hloc
  have hb0 := hB.2.1
  have hK := hB.2.2
  have hdisj' : Disjoint (Subgroup.zpowers b₀) (B.span ⊓ K) := by
    rw [hB.1]
    exact hdisj
  have hH1' : B.realized (Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers (B.b 1) : Set G)) = hSeven := hH1
  refine transvAll_of_mat B hB hord hdisj hodd fun {Mg} hMX hMn hMc hMne {p} hp hp2 hMp => ?_
  have hH : ∀ A ∈ hSeven, ∃ x ∈ (ggAutomizer ⊤ B.span).map B.glHom,
      (x : Matrix (Fin (7 + 1)) (Fin (7 + 1)) (ZMod 3)) = A := fun A hA =>
    B.exists_xg_of_realized (Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers (B.b 1) : Set G)) (by rw [hH1']; exact hA)
  have hstab : ∀ x ∈ (ggAutomizer ⊤ B.span).map B.glHom,
      (x : Matrix (Fin (7 + 1)) (Fin (7 + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1 →
      (∃ c : ZMod 3, (x : Matrix (Fin (7 + 1)) (Fin (7 + 1)) (ZMod 3)) *ᵥ Pi.single 1 1 =
        c • Pi.single 1 1) → (x : Matrix (Fin (7 + 1)) (Fin (7 + 1)) (ZMod 3)) ∈ hSeven :=
    fun x hx hxe hxc => by
      rw [← hH1']
      exact B.stab_mem_realized hb0 hx hxe hxc
  have hcard : Nat.card ↥((ggAutomizer ⊤ B.span).map B.glHom ⊓ fixE0 7) = 2903040 := by
    rw [card_xg_fixE0 B hb0]
    exact hcardC
  by_cases hp3 : p = 3
  · subst hp3
    exact e7_transv_of_normal3 hH hstab hcard
      (fun x hx hxe v hv => B.fix_preserves_A hb0 hord hK hdisj' hKn hx hxe v hv)
      (B.exists_xg_moves_e0 hb0 hfus) hMn hMp hMne
  · have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      by_contra hlt
      have h4 : p = 4 := by omega
      rw [h4] at hp
      exact absurd hp (by norm_num)
    exact absurd (e7_eq_bot hH hcard hMX hMn hMc hp hp5 hMp) hMne

theorem oddCoreTransvAt_E7 : OddCoreTransvAt Row.E7 := by
  intro G _ _ b₀ K E hstd B hB hloc hfus hodd
  obtain ⟨-, ⟨⟨hord, hKC, hKn, -⟩, -⟩, ⟨-, hdisj, -⟩⟩ := hstd
  exact transvAll_E7 B hB hord hdisj (fun g hg y hy => Subgroup.mem_subgroupOf.mp
    (hKn.conj_mem ⟨y, hKC hy⟩ (Subgroup.mem_subgroupOf.mpr hy) ⟨g, hg⟩)) hloc hfus hodd

end CFSG.StandardType.FrameRoute.FS81

end
