module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.ComponentAttachPart1

@[expose] public section

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.StandardType.F4ExplicitPos.BaseChange
open CFSG.StandardType.F4ExplicitPos.FixedImage
open CFSG.StandardType.F4ExplicitPos.AmbientAction
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

namespace CFSG.StandardType.F4ExplicitPos.ComponentAttach
variable {K L X : Type} [Field K] [Finite K] [Field L] [Algebra K L] [Group X] [Finite X]

theorem etaF4_map_centralizer
    (ψ : adjointGroup Tag.F4 K →* X) (G0 B1 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 K))
    (hcenter : Subgroup.center (adjointGroup Tag.F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (w : WeylGroup Tag.F4) {g0 : ModGL Tag.F4 L}
    (hg0C : g0 ∈ adjointGroup Tag.F4 L)
    (hg0 : ((frobF4 (K := K) (L := L) Fr hFr ⟨g0, hg0C⟩ : adjointGroup Tag.F4 L) :
      ModGL Tag.F4 L) = g0 * canonicalRep (coxeterSystem Tag.F4) L w)
    (D : Subgroup X) (hDB : D ≤ B1) :
    ((Subgroup.centralizer (D : Set X)).subgroupOf G0).map
        (etaF4 (L := L) ψ G0 hG0 hker hcenter g0) =
      (langDatumF4 (K := K) (L := L) Fr hFr w hg0C hg0).model ⊓
        Subgroup.centralizer
          (((D.subgroupOf B1).map
            (ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0)) :
            Set (ModGL Tag.F4 L)) := by
  classical
  have hRange := etaF4_range_model (K := K) (L := L) ψ G0 hG0 hker hcenter Fr hFr w hg0C hg0
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : (y : X) ∈ Subgroup.centralizer (D : Set X) := hy
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have hmem : etaF4 (L := L) ψ G0 hG0 hker hcenter g0 y ∈
          (etaF4 (L := L) ψ G0 hG0 hker hcenter g0).range := ⟨y, rfl⟩
      rwa [hRange] at hmem
    · rw [Subgroup.mem_centralizer_iff]
      rintro t ⟨b, hb, rfl⟩
      have hbD : (b : X) ∈ D := Subgroup.mem_subgroupOf.mp hb
      have hcommX : (b : X) * (y : X) = (y : X) * (b : X) := hy' (b : X) hbD
      have hfix : (G0.normalizerMonoidHom ⟨b, hBN b.property⟩) y = y := by
        apply Subtype.ext
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        change (b : X) * (y : X) * (b : X)⁻¹ = (y : X)
        rw [hcommX]
        group
      have hact := etaF4_action (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0 b y
      rw [hfix] at hact
      have h2 := congrArg (fun u : ModGL Tag.F4 L =>
        u * ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0 b) hact
      simpa [mul_assoc] using h2.symm
  · rintro hz
    obtain ⟨hzM, hzC⟩ := Subgroup.mem_inf.1 hz
    have hzrange : z ∈ (etaF4 (L := L) ψ G0 hG0 hker hcenter g0).range := by
      rw [hRange]
      exact hzM
    obtain ⟨y, rfl⟩ := hzrange
    refine Subgroup.mem_map.2 ⟨y, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro b hbD
    have hbB : b ∈ B1 := hDB hbD
    have hcommTheta : ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0
          ⟨b, hbB⟩ * etaF4 (L := L) ψ G0 hG0 hker hcenter g0 y =
        etaF4 (L := L) ψ G0 hG0 hker hcenter g0 y *
          ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0 ⟨b, hbB⟩ :=
      hzC _ (Subgroup.mem_map_of_mem _
        (Subgroup.mem_subgroupOf.mpr hbD))
    have hfix : (G0.normalizerMonoidHom ⟨b, hBN hbB⟩) y = y := by
      apply etaF4_injective ψ G0 hG0 hker hcenter g0
      rw [etaF4_action (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0 ⟨b, hbB⟩ y]
      rw [hcommTheta]
      group
    have hby : b * (y : X) = (y : X) * b := by
      have h := congrArg (fun t : G0 => (t : X)) hfix
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
      change (b : X) * (y : X) * (b : X)⁻¹ = (y : X) at h
      calc b * (y : X) = ((b : X) * (y : X) * (b : X)⁻¹) * b := by group
        _ = (y : X) * b := by rw [h]
    exact hby

theorem etaF4_map_centralizer_joint
    (ψ : adjointGroup Tag.F4 K →* X) (G0 B1 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 K))
    (hcenter : Subgroup.center (adjointGroup Tag.F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (w : WeylGroup Tag.F4) {g0 : ModGL Tag.F4 L}
    (hg0C : g0 ∈ adjointGroup Tag.F4 L)
    (hg0 : ((frobF4 (K := K) (L := L) Fr hFr ⟨g0, hg0C⟩ : adjointGroup Tag.F4 L) :
      ModGL Tag.F4 L) = g0 * canonicalRep (coxeterSystem Tag.F4) L w)
    (D : Subgroup X) (hDB : D ≤ B1) {x d : X} (hxD : x ∈ D) (hdD : d ∈ D)
    (hgen : Subgroup.closure ({x, d} : Set X) = D)
    (a_x a_d : Fin Tag.F4.rank → Lˣ)
    (hThetaX : ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0
        ⟨x, hDB hxD⟩ = rootDiagUnit Tag.F4 a_x)
    (hThetaD : ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0
        ⟨d, hDB hdD⟩ = rootDiagUnit Tag.F4 a_d) :
    ((Subgroup.centralizer (D : Set X)).subgroupOf G0).map
        (etaF4 (L := L) ψ G0 hG0 hker hcenter g0) =
      (langDatumF4 (K := K) (L := L) Fr hFr w hg0C hg0).model ⊓
        Subgroup.centralizer
          ({rootDiagUnit Tag.F4 a_x, rootDiagUnit Tag.F4 a_d} :
            Set (ModGL Tag.F4 L)) := by
  rw [etaF4_map_centralizer (K := K) (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner
    Fr hFr w hg0C hg0 D hDB]
  have hDsub : D.subgroupOf B1 =
      Subgroup.closure ({⟨x, hDB hxD⟩, ⟨d, hDB hdD⟩} : Set B1) := by
    apply Subgroup.map_injective (f := B1.subtype) Subtype.coe_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hDB, MonoidHom.map_closure,
      Set.image_insert_eq, Set.image_singleton]
    exact hgen.symm
  have himage : (D.subgroupOf B1).map
        (ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0) =
      Subgroup.closure ({rootDiagUnit Tag.F4 a_x, rootDiagUnit Tag.F4 a_d} :
        Set (ModGL Tag.F4 L)) := by
    rw [hDsub, MonoidHom.map_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl
      · exact Or.inl hThetaX
      · exact Or.inr hThetaD
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact ⟨⟨x, hDB hxD⟩, Or.inl rfl, hThetaX⟩
      · exact ⟨⟨d, hDB hdD⟩, Or.inr rfl, hThetaD⟩
  rw [himage, Subgroup.centralizer_closure]

theorem etaF4_map_centralizer_single
    (ψ : adjointGroup Tag.F4 K →* X) (G0 B1 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 K))
    (hcenter : Subgroup.center (adjointGroup Tag.F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (w : WeylGroup Tag.F4) {g0 : ModGL Tag.F4 L}
    (hg0C : g0 ∈ adjointGroup Tag.F4 L)
    (hg0 : ((frobF4 (K := K) (L := L) Fr hFr ⟨g0, hg0C⟩ : adjointGroup Tag.F4 L) :
      ModGL Tag.F4 L) = g0 * canonicalRep (coxeterSystem Tag.F4) L w)
    (D : Subgroup X) (hDB : D ≤ B1) {z : X} (hzD : z ∈ D)
    (a : Fin Tag.F4.rank → Lˣ)
    (hThetaZ : ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0
        ⟨z, hDB hzD⟩ = rootDiagUnit Tag.F4 a) :
    ((Subgroup.centralizer ({z} : Set X)).subgroupOf G0).map
        (etaF4 (L := L) ψ G0 hG0 hker hcenter g0) =
      (langDatumF4 (K := K) (L := L) Fr hFr w hg0C hg0).model ⊓
        Subgroup.centralizer ({rootDiagUnit Tag.F4 a} : Set (ModGL Tag.F4 L)) := by
  have hzB : z ∈ B1 := hDB hzD
  have hzpB : Subgroup.zpowers z ≤ B1 := Subgroup.zpowers_le.mpr hzB
  have hleft : Subgroup.centralizer (Subgroup.zpowers z : Set X) =
      Subgroup.centralizer ({z} : Set X) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [← hleft]
  rw [etaF4_map_centralizer (K := K) (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner
    Fr hFr w hg0C hg0 (Subgroup.zpowers z) hzpB]
  have hDsub : (Subgroup.zpowers z).subgroupOf B1 =
      Subgroup.zpowers (⟨z, hzB⟩ : B1) := by
    apply Subgroup.map_injective (f := B1.subtype) Subtype.coe_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hzpB, MonoidHom.map_zpowers]
    rfl
  have himage : ((Subgroup.zpowers z).subgroupOf B1).map
        (ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0) =
      Subgroup.zpowers (rootDiagUnit Tag.F4 a) := by
    rw [hDsub, MonoidHom.map_zpowers, hThetaZ]
  rw [himage, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem isComponentOf_map_commutator_inf
    {G G' : Type*} [Group G] [Group G'] (f : G →* G') (hf : Function.Injective f)
    {J Q : Subgroup G} {M C : Subgroup G'}
    (hJ : CFSG.Assembly.IsComponentOf J Q) (hperf : J = ⁅J, J⁆)
    (hmap : Q.map f = M ⊓ C) :
    CFSG.Assembly.IsComponentOf (J.map f) (⁅M, M⁆ ⊓ C) := by
  have hJmap : CFSG.Assembly.IsComponentOf (J.map f) (Q.map f) :=
    (isComponentOf_map_iff hf).2 hJ
  have hJQ : J.map f ≤ Q.map f := Subgroup.map_mono hJ.1
  have hJM : J.map f ≤ M := hJQ.trans (hmap.le.trans inf_le_left)
  have hJC : J.map f ≤ C := hJQ.trans (hmap.le.trans inf_le_right)
  have hJperf : J.map f = ⁅J.map f, J.map f⁆ := by
    calc J.map f = (⁅J, J⁆).map f := congrArg (Subgroup.map f) hperf
      _ = ⁅J.map f, J.map f⁆ := Subgroup.map_commutator J J f
  have hJGamma : J.map f ≤ ⁅M, M⁆ := by
    calc J.map f = ⁅J.map f, J.map f⁆ := hJperf
      _ ≤ ⁅M, M⁆ := Subgroup.commutator_mono hJM hJM
  have hH' : ⁅M, M⁆ ⊓ C ≤ Q.map f := by
    rw [hmap]
    exact inf_le_inf (Subgroup.commutator_le_self M) le_rfl
  exact isComponentOf_of_le hJmap (le_inf hJGamma hJC) hH'

theorem subgroupOf_isComponentOf
    (ψ : adjointGroup Tag.F4 K →* X) (G0 : Subgroup X) (_hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 K))
    (_hcenter : Subgroup.center (adjointGroup Tag.F4 K) = ⊥)
    {J Q : Subgroup X} (hJ : CFSG.Assembly.IsComponentOf J Q)
    (hJG : J ≤ G0) (hQG : Q ≤ G0) :
    CFSG.Assembly.IsComponentOf (J.subgroupOf G0) (Q.subgroupOf G0) := by
  apply (isComponentOf_map_iff (f := G0.subtype) Subtype.coe_injective).1
  simpa [Subgroup.map_subgroupOf_eq_of_le hJG, Subgroup.map_subgroupOf_eq_of_le hQG] using hJ

theorem subgroupOf_commutator_eq
    (ψ : adjointGroup Tag.F4 K →* X) (G0 : Subgroup X) (_hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 K))
    (_hcenter : Subgroup.center (adjointGroup Tag.F4 K) = ⊥)
    {J : Subgroup X} (hJG : J ≤ G0) (hperf : J = ⁅J, J⁆) :
    J.subgroupOf G0 = ⁅J.subgroupOf G0, J.subgroupOf G0⁆ := by
  apply Subgroup.map_injective (f := G0.subtype) Subtype.coe_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hJG, Subgroup.map_commutator,
    Subgroup.map_subgroupOf_eq_of_le hJG]
  exact hperf

theorem commutator_eq_of_isComponentOf
    {J Q : Subgroup X} (hJ : CFSG.Assembly.IsComponentOf J Q) :
    J = ⁅J, J⁆ := by
  have : Group.IsPerfect ↥J := ⟨hJ.2.2.1⟩
  exact Subgroup.commutator_eq_self.symm

theorem isComponentOf_eta_joint
    (ψ : adjointGroup Tag.F4 K →* X) (G0 B1 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 K))
    (hcenter : Subgroup.center (adjointGroup Tag.F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (w : WeylGroup Tag.F4) {g0 : ModGL Tag.F4 L}
    (hg0C : g0 ∈ adjointGroup Tag.F4 L)
    (hg0 : ((frobF4 (K := K) (L := L) Fr hFr ⟨g0, hg0C⟩ : adjointGroup Tag.F4 L) :
      ModGL Tag.F4 L) = g0 * canonicalRep (coxeterSystem Tag.F4) L w)
    (D : Subgroup X) (hDB : D ≤ B1) {x d : X} (hxD : x ∈ D) (hdD : d ∈ D)
    (hgen : Subgroup.closure ({x, d} : Set X) = D)
    (a_x a_d : Fin Tag.F4.rank → Lˣ)
    (hThetaX : ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0
        ⟨x, hDB hxD⟩ = rootDiagUnit Tag.F4 a_x)
    (hThetaD : ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0
        ⟨d, hDB hdD⟩ = rootDiagUnit Tag.F4 a_d)
    {J : Subgroup X}
    (hJ : CFSG.Assembly.IsComponentOf J (G0 ⊓ Subgroup.centralizer (D : Set X))) :
    CFSG.Assembly.IsComponentOf ((J.subgroupOf G0).map
        (etaF4 (L := L) ψ G0 hG0 hker hcenter g0))
      ((langDatumF4 (K := K) (L := L) Fr hFr w hg0C hg0).Γ ⊓
        Subgroup.centralizer
          ({rootDiagUnit Tag.F4 a_x, rootDiagUnit Tag.F4 a_d} :
            Set (ModGL Tag.F4 L))) := by
  have hJG : J ≤ G0 := hJ.1.trans inf_le_left
  have hQG : G0 ⊓ Subgroup.centralizer (D : Set X) ≤ G0 := inf_le_left
  have hcomp := subgroupOf_isComponentOf ψ G0 hG0 hker hcenter hJ hJG hQG
  have hQeq : (G0 ⊓ Subgroup.centralizer (D : Set X)).subgroupOf G0 =
      (Subgroup.centralizer (D : Set X)).subgroupOf G0 := by
    ext u
    simp [Subgroup.mem_subgroupOf]
  have hcomp' : CFSG.Assembly.IsComponentOf (J.subgroupOf G0)
      ((Subgroup.centralizer (D : Set X)).subgroupOf G0) := by
    simpa [hQeq] using hcomp
  have hperf := commutator_eq_of_isComponentOf hJ
  have hperf' := subgroupOf_commutator_eq ψ G0 hG0 hker hcenter hJG hperf
  have hmap := etaF4_map_centralizer_joint (K := K) (L := L) ψ G0 B1 hG0 hker hcenter
    hBN hinner Fr hFr w hg0C hg0 D hDB hxD hdD hgen a_x a_d hThetaX hThetaD
  exact isComponentOf_map_commutator_inf
    (etaF4 (L := L) ψ G0 hG0 hker hcenter g0)
    (etaF4_injective ψ G0 hG0 hker hcenter g0) hcomp' hperf' hmap

theorem isComponentOf_eta_single
    (ψ : adjointGroup Tag.F4 K →* X) (G0 B1 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 K))
    (hcenter : Subgroup.center (adjointGroup Tag.F4 K) = ⊥)
    (hBN : B1 ≤ Subgroup.normalizer (G0 : Set X))
    (hinner : ∀ b ∈ B1, ∃ g ∈ G0, b * g ∈ Subgroup.centralizer (G0 : Set X))
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (w : WeylGroup Tag.F4) {g0 : ModGL Tag.F4 L}
    (hg0C : g0 ∈ adjointGroup Tag.F4 L)
    (hg0 : ((frobF4 (K := K) (L := L) Fr hFr ⟨g0, hg0C⟩ : adjointGroup Tag.F4 L) :
      ModGL Tag.F4 L) = g0 * canonicalRep (coxeterSystem Tag.F4) L w)
    (D : Subgroup X) (hDB : D ≤ B1) {z : X} (hzD : z ∈ D)
    (a : Fin Tag.F4.rank → Lˣ)
    (hThetaZ : ThetaF4 (L := L) ψ G0 B1 hG0 hker hcenter hBN hinner g0
        ⟨z, hDB hzD⟩ = rootDiagUnit Tag.F4 a)
    {J : Subgroup X}
    (hJ : CFSG.Assembly.IsComponentOf J (G0 ⊓ Subgroup.centralizer ({z} : Set X))) :
    CFSG.Assembly.IsComponentOf ((J.subgroupOf G0).map
        (etaF4 (L := L) ψ G0 hG0 hker hcenter g0))
      ((langDatumF4 (K := K) (L := L) Fr hFr w hg0C hg0).Γ ⊓
        Subgroup.centralizer ({rootDiagUnit Tag.F4 a} : Set (ModGL Tag.F4 L))) := by
  have hJG : J ≤ G0 := hJ.1.trans inf_le_left
  have hQG : G0 ⊓ Subgroup.centralizer ({z} : Set X) ≤ G0 := inf_le_left
  have hcomp := subgroupOf_isComponentOf ψ G0 hG0 hker hcenter hJ hJG hQG
  have hQeq : (G0 ⊓ Subgroup.centralizer ({z} : Set X)).subgroupOf G0 =
      (Subgroup.centralizer ({z} : Set X)).subgroupOf G0 := by
    ext u
    simp [Subgroup.mem_subgroupOf]
  have hcomp' : CFSG.Assembly.IsComponentOf (J.subgroupOf G0)
      ((Subgroup.centralizer ({z} : Set X)).subgroupOf G0) := by
    simpa [hQeq] using hcomp
  have hperf := commutator_eq_of_isComponentOf hJ
  have hperf' := subgroupOf_commutator_eq ψ G0 hG0 hker hcenter hJG hperf
  have hmap := etaF4_map_centralizer_single (K := K) (L := L) ψ G0 B1 hG0 hker hcenter
    hBN hinner Fr hFr w hg0C hg0 D hDB hzD a hThetaZ
  exact isComponentOf_map_commutator_inf
    (etaF4 (L := L) ψ G0 hG0 hker hcenter g0)
    (etaF4_injective ψ G0 hG0 hker hcenter g0) hcomp' hperf' hmap

end CFSG.StandardType.F4ExplicitPos.ComponentAttach
end

end
