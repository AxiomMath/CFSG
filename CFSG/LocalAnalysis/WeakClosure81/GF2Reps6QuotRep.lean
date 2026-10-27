module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6Sec
public import CFSG.LocalAnalysis.WeakClosure81.W18Asch66
import CFSG.LocalAnalysis.GL83PartI.I_24_3.Basic
import CFSG.Quasithin.EmptyFaithful.SBd14Ind
public import CFSG.Quasithin.Background.AutOnBasics

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open CFSG.Quasithin Subgroup

private lemma exists_stab_quot {Q : Type} [Group Q] {V : Type} [CommGroup V] [Finite V]
    (ρ : Q →* MulAut V) (hρ : Function.Injective ρ) {L A : Subgroup Q}
    (hL : CFSG.Open.IsQuasisimple ↥L) (hAL : A ≤ Subgroup.normalizer (L : Set Q)) :
    ∃ W : Subgroup V,
      A.map ρ ⊔ L.map ρ ≤ stabSub W ∧ ¬ L.map ρ ≤ centQuot W ∧
      (∀ g ∈ A.map ρ ⊔ L.map ρ, ∀ l ∈ L.map ρ, g * l * g⁻¹ ∈ L.map ρ) ∧
      ∀ v : V, (∀ l ∈ L.map ρ, l v * v⁻¹ ∈ W) → v ∈ W := by
  classical
  let L₁ : Subgroup (MulAut V) := L.map ρ
  let A₁ : Subgroup (MulAut V) := A.map ρ
  let G : Subgroup (MulAut V) := A₁ ⊔ L₁
  have hrange : (ρ.comp L.subtype).range = L₁ := by
    ext x
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨l, l.2, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨l, hl⟩, rfl⟩
  have hperfMap : (commutator ↥L).map (ρ.comp L.subtype) = ⁅L₁, L₁⁆ := by
    rw [map_commutator_eq, hrange]
  have hperfL₁ : ⁅L₁, L₁⁆ = L₁ := by
    rw [← hperfMap, hL.1, ← MonoidHom.range_eq_map, hrange]
  have hcenter_ne_top : Subgroup.center ↥L ≠ ⊤ := by
    have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.2
    exact QuotientGroup.nontrivial_iff.mp inferInstance
  have hLne : L ≠ ⊥ := by
    intro hbot
    apply hcenter_ne_top
    rw [hbot]
    have : IsMulCommutative ↥(⊥ : Subgroup Q) :=
      ⟨⟨fun a b => Subsingleton.elim (a * b) (b * a)⟩⟩
    exact Subgroup.center_eq_top
  have hL₁ne : L₁ ≠ ⊥ := by
    intro hbot
    apply hLne
    exact (Subgroup.map_eq_bot_iff_of_injective L hρ).mp hbot
  have hA₁leG : A₁ ≤ G := le_sup_left
  have hL₁leG : L₁ ≤ G := le_sup_right
  have hA₁norm : A₁ ≤ Subgroup.normalizer (L₁ : Set (MulAut V)) :=
    (Subgroup.map_mono hAL).trans (Subgroup.le_normalizer_map ρ)
  have hL₁norm : L₁ ≤ Subgroup.normalizer (L₁ : Set (MulAut V)) :=
    Subgroup.le_normalizer
  have hGnorm : G ≤ Subgroup.normalizer (L₁ : Set (MulAut V)) :=
    sup_le hA₁norm hL₁norm
  have hnorm : ∀ g ∈ G, ∀ l ∈ L₁, g * l * g⁻¹ ∈ L₁ := by
    intro g hg l hl
    exact (Subgroup.mem_normalizer_iff.mp (hGnorm hg) l).mp hl
  obtain ⟨W, hGW, hWnon, hfixW⟩ :=
    exists_quot_fixV_eq_bot hL₁leG hnorm hperfL₁ hL₁ne
  exact ⟨W, hGW, hWnon, hnorm, hfixW⟩

private lemma exists_theta {Q : Type} [Group Q] {V : Type} [CommGroup V]
    (ρ : Q →* MulAut V) {L : Subgroup Q} (hL : CFSG.Open.IsQuasisimple ↥L)
    (hZ : Odd (Nat.card (Subgroup.center ↥L))) {W : Subgroup V}
    (hstabL : L.map ρ ≤ stabSub W) (hWnon : ¬ L.map ρ ≤ centQuot W) :
    ∃ (θ : ↥L →* ↥(autQuot (L.map ρ) W)) (ι : ↥L →* stabSub W),
      (∀ l : ↥L, (ι l : MulAut V) = ρ (l : Q)) ∧
      (∀ l : ↥L, (θ l : MulAut (V ⧸ W)) = quotHom W (ι l)) ∧
      Function.Surjective θ ∧ θ.ker ≤ Subgroup.center ↥L ∧
      CFSG.Open.IsQuasisimple ↥(autQuot (L.map ρ) W) ∧
      Odd (Nat.card (Subgroup.center ↥(autQuot (L.map ρ) W))) ∧
      Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃*
        (↥(autQuot (L.map ρ) W) ⧸ Subgroup.center ↥(autQuot (L.map ρ) W))) := by
  classical
  let Lbar : Subgroup (MulAut (V ⧸ W)) := autQuot (L.map ρ) W
  let ι : ↥L →* stabSub W :=
    { toFun := fun l => ⟨ρ (l : Q), hstabL ⟨l, l.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hι : ∀ l : ↥L, (ι l : MulAut V) = ρ (l : Q) := fun _ => rfl
  let f : ↥L →* MulAut (V ⧸ W) := (quotHom W).comp ι
  let θ : ↥L →* ↥Lbar :=
    f.codRestrict Lbar fun l => mem_autQuot.mpr ⟨ι l, ⟨l, l.2, rfl⟩, rfl⟩
  have hθ : ∀ l : ↥L, (θ l : MulAut (V ⧸ W)) = quotHom W (ι l) := fun _ => rfl
  have hθsurj : Function.Surjective θ := by
    intro x
    obtain ⟨g, hgL, hgx⟩ := mem_autQuot.mp x.2
    obtain ⟨l, hl, hgl⟩ := Subgroup.mem_map.mp hgL
    refine ⟨⟨l, hl⟩, ?_⟩
    apply Subtype.ext
    change quotHom W (ι ⟨l, hl⟩) = (x : MulAut (V ⧸ W))
    rw [show ι ⟨l, hl⟩ = g from Subtype.ext hgl]
    exact hgx
  have hθker : θ.ker ≤ Subgroup.center ↥L := by
    rcases GL83.I243.normal_le_center_or_eq_top hL θ.ker with h | h
    · exact h
    · exfalso
      apply hWnon
      intro x hx
      obtain ⟨l, hl, hxl⟩ := Subgroup.mem_map.mp hx
      have h1 : (⟨l, hl⟩ : ↥L) ∈ θ.ker := by rw [h]; trivial
      have h2 : (θ ⟨l, hl⟩ : ↥Lbar) = 1 := MonoidHom.mem_ker.mp h1
      have h3 : quotHom W (ι ⟨l, hl⟩) = 1 := congrArg Subtype.val h2
      have h4 : ι ⟨l, hl⟩ ∈ (quotHom W).ker := MonoidHom.mem_ker.mpr h3
      rw [ker_quotHom] at h4
      have h5 : (ι ⟨l, hl⟩ : MulAut V) ∈ centQuot W := Subgroup.mem_subgroupOf.mp h4
      exact hxl ▸ h5
  have hperfL : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hL.1
  have hcomap : (Subgroup.center ↥Lbar).comap θ = Subgroup.center ↥L :=
    CFSG.LocalCores.comap_center_eq_of_perfect hperfL θ hθsurj hθker
  have hcentermap : (Subgroup.center ↥L).map θ = Subgroup.center ↥Lbar := by
    rw [← hcomap, Subgroup.map_comap_eq_self_of_surjective hθsurj]
  have hZbar : Odd (Nat.card (Subgroup.center ↥Lbar)) := by
    rw [← hcentermap]
    exact hZ.of_dvd_nat (Subgroup.card_map_dvd (Subgroup.center ↥L) θ)
  let φ : ↥L →* (↥Lbar ⧸ Subgroup.center ↥Lbar) :=
    (QuotientGroup.mk' (Subgroup.center ↥Lbar)).comp θ
  have hφsurj : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective _).comp hθsurj
  have hφker : φ.ker = Subgroup.center ↥L := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcomap]
  let e : (↥L ⧸ Subgroup.center ↥L) ≃* (↥Lbar ⧸ Subgroup.center ↥Lbar) :=
    (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)
  have hperfLbar : Group.IsPerfect ↥Lbar := by
    have : Group.IsPerfect ↥L := hperfL
    exact Group.IsPerfect.ofSurjective hθsurj
  have hLbarqs : CFSG.Open.IsQuasisimple ↥Lbar := by
    have hsimple : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.2
    exact ⟨Group.isPerfect_def.mp hperfLbar, e.symm.isSimpleGroup⟩
  exact ⟨θ, ι, hι, hθ, hθsurj, hθker, hLbarqs, hZbar, ⟨e⟩⟩

private lemma mem_centralizer_of_comm {Q : Type} [Group Q] {V : Type} [CommGroup V]
    (ρ : Q →* MulAut V) {L : Subgroup Q} {W : Subgroup V}
    {Lbar : Subgroup (MulAut (V ⧸ W))} (ι : ↥L →* stabSub W) (θ : ↥L →* ↥Lbar)
    (hperfL : Group.IsPerfect ↥L) (hθker : θ.ker ≤ Subgroup.center ↥L)
    (hι : ∀ l : ↥L, (ι l : MulAut V) = ρ (l : Q))
    (hθ : ∀ l : ↥L, (θ l : MulAut (V ⧸ W)) = quotHom W (ι l))
    {u : Q} (hu : u ∈ Subgroup.normalizer (L : Set Q)) {g : stabSub W}
    (hgu : ρ u = (g : MulAut V))
    (hcomm : ∀ l : ↥L, quotHom W g * (θ l : MulAut (V ⧸ W)) =
      (θ l : MulAut (V ⧸ W)) * quotHom W g) :
    u ∈ Subgroup.centralizer (L : Set Q) := by
  let ψ : MulAut ↥L := conjAct L ⟨u, hu⟩
  have hψcoe : ∀ l : ↥L, ((ψ l : ↥L) : Q) = u * (l : Q) * u⁻¹ := fun l =>
    CFSG.Quasithin.AutOn.coe_conjAct_apply L ⟨u, hu⟩ l
  have hθconj : ∀ l : ↥L,
      (θ (ψ l) : MulAut (V ⧸ W)) = (quotHom W g : MulAut (V ⧸ W)) *
        (θ l : MulAut (V ⧸ W)) * (quotHom W g : MulAut (V ⧸ W))⁻¹ := by
    intro l
    have hsub : ι (ψ l) = g * ι l * g⁻¹ := by
      apply Subtype.ext
      rw [hι, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hι]
      have h := congrArg (fun z : Q => ρ z) (hψcoe l)
      simpa [map_mul, hgu] using h
    calc (θ (ψ l) : MulAut (V ⧸ W)) = quotHom W (ι (ψ l)) := hθ (ψ l)
      _ = quotHom W (g * ι l * g⁻¹) := by rw [hsub]
      _ = (quotHom W g : MulAut (V ⧸ W)) * (quotHom W (ι l) : MulAut (V ⧸ W)) *
            (quotHom W g : MulAut (V ⧸ W))⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = (quotHom W g : MulAut (V ⧸ W)) * (θ l : MulAut (V ⧸ W)) *
            (quotHom W g : MulAut (V ⧸ W))⁻¹ := by rw [← hθ l]
  have hψcen : ∀ l : ↥L, ψ l * l⁻¹ ∈ Subgroup.center ↥L := by
    intro l
    apply hθker
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    apply Subtype.ext
    change (θ (ψ l) : MulAut (V ⧸ W)) * ((θ l : MulAut (V ⧸ W)))⁻¹ = 1
    rw [hθconj l, hcomm l]
    group
  have hψ : ψ = 1 := CFSG.Quasithin.SBd14.eq_one_of_central_perfect hperfL ψ hψcen
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h2 := congrArg (fun φ : MulAut ↥L => ((φ ⟨l, hl⟩ : ↥L) : Q)) hψ
  simp only [hψcoe, MulAut.one_apply] at h2
  calc l * u = (u * l * u⁻¹) * u := by rw [h2]
    _ = u * l := by group

private lemma thetaA_surjective {Q : Type} [Group Q] {V : Type} [CommGroup V]
    (ρ : Q →* MulAut V) {A : Subgroup Q} {W : Subgroup V} (ιA : ↥A →* stabSub W)
    (θA : ↥A →* ↥(autQuot (A.map ρ) W))
    (hιA : ∀ a : ↥A, (ιA a : MulAut V) = ρ (a : Q))
    (hθA : ∀ a : ↥A, (θA a : MulAut (V ⧸ W)) = quotHom W (ιA a)) :
    Function.Surjective θA := by
  intro x
  obtain ⟨g, hgA, hgx⟩ := mem_autQuot.mp x.2
  obtain ⟨a, ha, hga⟩ := Subgroup.mem_map.mp hgA
  refine ⟨⟨a, ha⟩, ?_⟩
  apply Subtype.ext
  rw [hθA, show ιA ⟨a, ha⟩ = g from Subtype.ext (by rw [hιA]; exact hga)]
  exact hgx

private lemma abar_facts {Q : Type} [Group Q] {V : Type} [CommGroup V]
    (ρ : Q →* MulAut V) {L A : Subgroup Q} {W : Subgroup V}
    (ι : ↥L →* stabSub W) (ιA : ↥A →* stabSub W)
    (θ : ↥L →* ↥(autQuot (L.map ρ) W)) (θA : ↥A →* ↥(autQuot (A.map ρ) W))
    (hperfL : Group.IsPerfect ↥L) (hθker : θ.ker ≤ Subgroup.center ↥L)
    (hι : ∀ l : ↥L, (ι l : MulAut V) = ρ (l : Q))
    (hθ : ∀ l : ↥L, (θ l : MulAut (V ⧸ W)) = quotHom W (ι l))
    (hιA : ∀ a : ↥A, (ιA a : MulAut V) = ρ (a : Q))
    (hθA : ∀ a : ↥A, (θA a : MulAut (V ⧸ W)) = quotHom W (ιA a))
    (hsurjA : Function.Surjective θA) (hA4 : Nat.card A = 4)
    (hA2 : ∀ a ∈ A, a * a = 1) (hAC : A ⊓ Subgroup.centralizer (L : Set Q) = ⊥)
    (hAL : A ≤ Subgroup.normalizer (L : Set Q))
    {G : Subgroup (MulAut V)} (hA_le : A.map ρ ≤ G)
    (hnorm : ∀ g ∈ G, ∀ l ∈ L.map ρ, g * l * g⁻¹ ∈ L.map ρ)
    (hstabL : L.map ρ ≤ stabSub W)
    (hfixW : ∀ v : V, (∀ l ∈ L.map ρ, l v * v⁻¹ ∈ W) → v ∈ W)
    (hAQ : IsQuadratic (A.map ρ)) :
    Nat.card (autQuot (A.map ρ) W) = 4 ∧
      (∀ u ∈ autQuot (A.map ρ) W, u * u = 1) ∧
      (∀ u ∈ autQuot (A.map ρ) W, ∀ l ∈ autQuot (L.map ρ) W,
        u * l * u⁻¹ ∈ autQuot (L.map ρ) W) ∧
      autQuot (A.map ρ) W ⊓
        Subgroup.centralizer (autQuot (L.map ρ) W : Set (MulAut (V ⧸ W))) = ⊥ ∧
      IsQuadratic (autQuot (A.map ρ) W) ∧ fixV (autQuot (L.map ρ) W) = ⊥ := by
  have hinjA : Function.Injective θA := by
    intro a b hab
    have h1 : θA (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : quotHom W (ιA (a * b⁻¹)) = 1 := by
      rw [← hθA]
      exact congrArg Subtype.val h1
    have hu : ((a * b⁻¹ : ↥A) : Q) = 1 := by
      have hmem : ((a * b⁻¹ : ↥A) : Q) ∈ A ⊓ Subgroup.centralizer (L : Set Q) :=
        ⟨(a * b⁻¹).2, mem_centralizer_of_comm (g := ιA (a * b⁻¹)) ρ ι θ hperfL hθker
          hι hθ (hAL (a * b⁻¹).2) (hιA _).symm (by
            intro l
            rw [h2]
            simp)⟩
      rw [hAC] at hmem
      exact Subgroup.mem_bot.mp hmem
    exact mul_inv_eq_one.mp (Subtype.ext hu)
  have hA4bar : Nat.card (autQuot (A.map ρ) W) = 4 := by
    have hbij : Function.Bijective θA := ⟨hinjA, hsurjA⟩
    have hcard : Nat.card (autQuot (A.map ρ) W) = Nat.card A :=
      (Nat.card_congr (Equiv.ofBijective θA hbij)).symm
    rw [hA4] at hcard
    exact hcard
  have hA2bar : ∀ u ∈ autQuot (A.map ρ) W, u * u = 1 := by
    intro u hu
    obtain ⟨a, ha⟩ := hsurjA ⟨u, hu⟩
    have hcoe : (θA a : MulAut (V ⧸ W)) = u := congrArg Subtype.val ha
    rw [← hcoe, ← Subgroup.coe_mul, ← map_mul]
    have h2 : a * a = 1 := by
      apply Subtype.ext
      exact hA2 (a : Q) a.2
    rw [h2, map_one]
    simp
  have hALbar : ∀ u ∈ autQuot (A.map ρ) W, ∀ l ∈ autQuot (L.map ρ) W,
      u * l * u⁻¹ ∈ autQuot (L.map ρ) W := by
    intro u hu l hl
    obtain ⟨g, hgA, hgu⟩ := mem_autQuot.mp hu
    obtain ⟨l₀, hl₀, hgl⟩ := mem_autQuot.mp hl
    rw [← hgu, ← hgl]
    have hconj : ((g * l₀ * g⁻¹ : stabSub W) : MulAut V) ∈ L.map ρ := by
      have hgG : (g : MulAut V) ∈ G := hA_le hgA
      simpa using hnorm (g : MulAut V) hgG (l₀ : MulAut V) hl₀
    refine mem_autQuot.mpr ⟨g * l₀ * g⁻¹, hconj, ?_⟩
    simp [map_mul, map_inv]
  have hACbar : autQuot (A.map ρ) W ⊓
      Subgroup.centralizer (autQuot (L.map ρ) W : Set (MulAut (V ⧸ W))) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hxA, hxC⟩
    obtain ⟨g, hgA, hgx⟩ := mem_autQuot.mp hxA
    obtain ⟨u, hu, hgu⟩ := Subgroup.mem_map.mp hgA
    have hcomm : ∀ l : ↥L, quotHom W g * (θ l : MulAut (V ⧸ W)) =
        (θ l : MulAut (V ⧸ W)) * quotHom W g := by
      intro l
      have h := Subgroup.mem_centralizer_iff.mp hxC (θ l) (θ l).2
      rw [← hgx] at h
      exact h.symm
    have huc : u ∈ Subgroup.centralizer (L : Set Q) :=
      mem_centralizer_of_comm (g := g) ρ ι θ hperfL hθker hι hθ (hAL hu) hgu hcomm
    have hu1 : u = 1 := by
      have hmem : u ∈ A ⊓ Subgroup.centralizer (L : Set Q) := ⟨hu, huc⟩
      rw [hAC] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hg1 : g = 1 := by
      apply Subtype.ext
      rw [← hgu, hu1, map_one]
      simp
    rw [← hgx, hg1, map_one]
  have hfixbar : fixV (autQuot (L.map ρ) W) = ⊥ := fixV_autQuot_eq_bot hstabL hfixW
  have hAbar : IsQuadratic (autQuot (A.map ρ) W) := isQuadratic_autQuot hAQ W
  exact ⟨hA4bar, hA2bar, hALbar, hACbar, hAbar, hfixbar⟩

private lemma inner_transfer {Q : Type} [Group Q] {V : Type} [CommGroup V]
    (ρ : Q →* MulAut V) {L A : Subgroup Q} {W : Subgroup V}
    (ι : ↥L →* stabSub W) (ιA : ↥A →* stabSub W)
    (θ : ↥L →* ↥(autQuot (L.map ρ) W)) (θA : ↥A →* ↥(autQuot (A.map ρ) W))
    (hperfL : Group.IsPerfect ↥L) (hθker : θ.ker ≤ Subgroup.center ↥L)
    (hι : ∀ l : ↥L, (ι l : MulAut V) = ρ (l : Q))
    (hθ : ∀ l : ↥L, (θ l : MulAut (V ⧸ W)) = quotHom W (ι l))
    (hιA : ∀ a : ↥A, (ιA a : MulAut V) = ρ (a : Q))
    (hθA : ∀ a : ↥A, (θA a : MulAut (V ⧸ W)) = quotHom W (ιA a))
    (hθsurj : Function.Surjective θ) (hAL : A ≤ Subgroup.normalizer (L : Set Q))
    (hinner : ∀ u ∈ autQuot (A.map ρ) W, ∃ l ∈ autQuot (L.map ρ) W,
      u * l⁻¹ ∈ Subgroup.centralizer (autQuot (L.map ρ) W : Set (MulAut (V ⧸ W)))) :
    ∀ a ∈ A, ∃ l ∈ L, a * l⁻¹ ∈ Subgroup.centralizer (L : Set Q) := by
  intro a ha
  obtain ⟨lbar, hlbar, hcen⟩ := hinner (θA ⟨a, ha⟩) (θA ⟨a, ha⟩).2
  obtain ⟨l, hl⟩ := hθsurj ⟨lbar, hlbar⟩
  have hlcoe : (θ l : MulAut (V ⧸ W)) = lbar := congrArg Subtype.val hl
  rw [← hlcoe] at hcen
  refine ⟨l, l.2, ?_⟩
  have hu : a * (l : Q)⁻¹ ∈ Subgroup.normalizer (L : Set Q) :=
    Subgroup.mul_mem _ (hAL ha) (Subgroup.inv_mem _ (Subgroup.le_normalizer l.2))
  have hg : ρ (a * (l : Q)⁻¹) = ((ιA ⟨a, ha⟩ * (ι l)⁻¹ : stabSub W) : MulAut V) := by
    rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hιA, hι]
  have hcomm : ∀ l' : ↥L,
      quotHom W (ιA ⟨a, ha⟩ * (ι l)⁻¹) * (θ l' : MulAut (V ⧸ W)) =
        (θ l' : MulAut (V ⧸ W)) * quotHom W (ιA ⟨a, ha⟩ * (ι l)⁻¹) := by
    intro l'
    have hcoe : (quotHom W (ιA ⟨a, ha⟩ * (ι l)⁻¹) : MulAut (V ⧸ W)) =
        (θA ⟨a, ha⟩ : MulAut (V ⧸ W)) * (θ l : MulAut (V ⧸ W))⁻¹ := by
      rw [map_mul, map_inv, hθA, hθ]
    rw [hcoe]
    exact (Subgroup.mem_centralizer_iff.mp hcen (θ l') (θ l').2).symm
  exact mem_centralizer_of_comm (g := ιA ⟨a, ha⟩ * (ι l)⁻¹) ρ ι θ hperfL hθker hι hθ hu
    hg hcomm

theorem exists_quot_of_rep {Q : Type} [Group Q] [Finite Q] {V : Type} [CommGroup V]
    [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (ρ : Q →* MulAut V) (hρ : Function.Injective ρ)
    {L A : Subgroup Q} (hL : CFSG.Open.IsQuasisimple ↥L) (hZ : Odd (Nat.card (center ↥L)))
    (hAL : A ≤ normalizer (L : Set Q)) (hA4 : Nat.card A = 4) (hA2 : ∀ a ∈ A, a * a = 1)
    (hq : CFSG.LocalAnalysis.WeakClosure81.IsQuadraticOn ρ A)
    (hAC : A ⊓ centralizer (L : Set Q) = ⊥) :
    ∃ (W : Type) (_ : CommGroup W) (_ : Finite W) (L' A' : Subgroup (MulAut W)),
      (∀ w : W, w ^ 2 = 1) ∧ CFSG.Open.IsQuasisimple ↥L' ∧ Odd (Nat.card (center ↥L')) ∧
      Nonempty ((↥L ⧸ center ↥L) ≃* (↥L' ⧸ center ↥L')) ∧
      (∀ u ∈ A', ∀ l ∈ L', u * l * u⁻¹ ∈ L') ∧ Nat.card A' = 4 ∧ (∀ u ∈ A', u * u = 1) ∧
      IsQuadratic A' ∧ A' ⊓ centralizer (L' : Set (MulAut W)) = ⊥ ∧ fixV L' = ⊥ ∧
      ((∀ u ∈ A', ∃ l ∈ L', u * l⁻¹ ∈ centralizer (L' : Set (MulAut W))) →
        ∀ a ∈ A, ∃ l ∈ L, a * l⁻¹ ∈ centralizer (L : Set Q)) := by
  classical
  obtain ⟨W, hGW, hWnon, hnorm, hfixW⟩ := exists_stab_quot ρ hρ hL hAL
  have hstabL : L.map ρ ≤ stabSub W := le_sup_right.trans hGW
  have hstabA : A.map ρ ≤ stabSub W := le_sup_left.trans hGW
  obtain ⟨θ, ι, hι, hθ, hθsurj, hθker, hLbarqs, hZbar, hiso⟩ :=
    exists_theta ρ hL hZ hstabL hWnon
  let ιA : ↥A →* stabSub W :=
    { toFun := fun a => ⟨ρ (a : Q), hstabA ⟨a, a.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hιA : ∀ a : ↥A, (ιA a : MulAut V) = ρ (a : Q) := fun _ => rfl
  let θA : ↥A →* ↥(autQuot (A.map ρ) W) :=
    ((quotHom W).comp ιA).codRestrict _
      fun a => mem_autQuot.mpr ⟨ιA a, ⟨a, a.2, rfl⟩, rfl⟩
  have hθA : ∀ a : ↥A, (θA a : MulAut (V ⧸ W)) = quotHom W (ιA a) := fun _ => rfl
  have hsurjA : Function.Surjective θA := thetaA_surjective ρ ιA θA hιA hθA
  have hperfL : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hL.1
  have hAQ : IsQuadratic (A.map ρ) := by
    rw [IsQuadratic, commV, Subgroup.closure_le]
    rintro w ⟨x, hx, v, rfl⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    refine (mem_fixV (X := A.map ρ) (v := ρ a v * v⁻¹)).mpr ?_
    intro b hb
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    exact hq a ha b' hb' v
  obtain ⟨hA4bar, hA2bar, hALbar, hACbar, hAbar, hfixbar⟩ :=
    abar_facts ρ ι ιA θ θA hperfL hθker hι hθ hιA hθA hsurjA hA4 hA2 hAC hAL
      le_sup_left hnorm hstabL hfixW hAQ
  have hVquot : ∀ v : V ⧸ W, v ^ 2 = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow, hV x]
      simp
  refine ⟨V ⧸ W, inferInstance, inferInstance, autQuot (L.map ρ) W, autQuot (A.map ρ) W,
    hVquot, hLbarqs, hZbar, hiso, hALbar, hA4bar, hA2bar, hAbar, hACbar, hfixbar, ?_⟩
  intro hinner
  exact inner_transfer ρ ι ιA θ θA hperfL hθker hι hθ hιA hθA hθsurj hAL hinner

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
