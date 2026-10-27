module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNotExcRows
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSThreeBar

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Generic

theorem ggRCS_solvable_normal_le_center {Q : Type} [Group Q]
    (hQ : CFSG.Open.IsQuasisimple Q) {W : Subgroup Q} [W.Normal]
    (hs : Group.IsSolvable ↥W) : W ≤ Subgroup.center Q := by
  have hQn : CFSG.IsQuasisimple Q :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native Q).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open Q).mpr hQ)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQn (N := W) inferInstance with
    htop | hcen
  · exfalso
    have htop' : Group.IsSolvable ↥(⊤ : Subgroup Q) := htop ▸ hs
    haveI : Group.IsSolvable ↥(⊤ : Subgroup Q) := htop'
    have hsol : Group.IsSolvable Q :=
      Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := Q)).toMonoidHom)
        (Subgroup.topEquiv (G := Q)).surjective
    haveI : Group.IsSolvable Q := hsol
    haveI : Group.IsPerfect Q := ⟨hQ.1⟩
    haveI : Nontrivial Q := CFSG.LocalCores.isQuasisimple_nontrivial hQn
    exact Group.IsPerfect.not_isSolvable Q hsol
  · exact hcen

theorem ggRCS_isComponentOf_map_mulAut {A : Type} [Group A] (α : MulAut A) {C : Subgroup A}
    (hC : CFSG.Open.IsComponentOf C ⊤) :
    CFSG.Open.IsComponentOf (C.map α.toMonoidHom) ⊤ := by
  have hsub : CFSG.Open.IsSubnormal (C.map α.toMonoidHom) ⊤ := by
    have h := hC.2.1.map α.toMonoidHom
    rwa [Subgroup.map_top_of_surjective α.toMonoidHom α.surjective] at h
  have hq : CFSG.Open.IsQuasisimple ↥(C.map α.toMonoidHom) :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (C.equivMapOfInjective α.toMonoidHom α.injective).symm hC.2.2
  exact ⟨le_top, hsub, hq⟩

theorem ggRCS_isSolvable_map_of_comm {A B : Type} [Group A] [Group B] (f : A →* B)
    {H : Subgroup A} (hH : ∀ a b : H, a * b = b * a) :
    Group.IsSolvable ↥(H.map f) := by
  refine Group.isSolvable_of_comm fun a b => Subtype.ext ?_
  obtain ⟨a₀, ha₀, hae⟩ := Subgroup.mem_map.mp a.2
  obtain ⟨b₀, hb₀, hbe⟩ := Subgroup.mem_map.mp b.2
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hae, ← hbe]
  simpa only [Subgroup.coe_mul, map_mul] using
    congrArg (fun z : ↥H => f (z : A)) (hH ⟨a₀, ha₀⟩ ⟨b₀, hb₀⟩)

theorem ggRCS_commute_of_mem_map {A B : Type} [Group A] [Group B] (f : A →* B)
    {H : Subgroup A} (hH : ∀ a b : H, a * b = b * a) {a b : B}
    (ha : a ∈ H.map f) (hb : b ∈ H.map f) : Commute a b := by
  obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
  have hc : Commute a₀ b₀ :=
    congrArg (fun z : ↥H => (z : A)) (hH ⟨a₀, ha₀⟩ ⟨b₀, hb₀⟩)
  exact Commute.map hc f

theorem ggRCS_center_eq_bot_of_isSimpleGroup_of_isPerfect {Q : Type} [Group Q]
    [IsSimpleGroup Q] (hQ : Group.IsPerfect Q) : Subgroup.center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : Q, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm
    haveI : Group.IsSolvable Q := Group.isSolvable_of_comm hcomm
    haveI : Group.IsPerfect Q := hQ
    exact Group.IsPerfect.not_isSolvable Q inferInstance

theorem ggRCSImg_conj_eq {A : Type} [Group A] {H N : Subgroup A} {g : A}
    (hgN : g ∈ N) (hgH : g ∈ Subgroup.normalizer (H : Set A)) :
    ((H.subgroupOf N).map (QuotientGroup.mk' (CFSG.pCore 2 ↥N))).map
        (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥N) ⟨g, hgN⟩)).toMonoidHom =
      (H.subgroupOf N).map (QuotientGroup.mk' (CFSG.pCore 2 ↥N)) := by
  classical
  let P : Subgroup ↥N := CFSG.pCore 2 ↥N
  let π : ↥N →* (↥N ⧸ P) := QuotientGroup.mk' P
  let gb : ↥N := ⟨g, hgN⟩
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨gb * a * gb⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      have haH : (a : A) ∈ H := Subgroup.mem_subgroupOf.mp ha
      have hh : g * (a : A) * g⁻¹ ∈ H :=
        (Subgroup.mem_normalizer_iff.mp hgH (a : A)).mp haH
      simpa [gb] using hh
    · change (QuotientGroup.mk' P) (gb * a * gb⁻¹) =
        MulAut.conj ((QuotientGroup.mk' P) gb) ((QuotientGroup.mk' P) a)
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
  · intro hz
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hz
    have hpre : gb⁻¹ * a * gb ∈ H.subgroupOf N := by
      rw [Subgroup.mem_subgroupOf]
      have haH : (a : A) ∈ H := Subgroup.mem_subgroupOf.mp ha
      have hh : g⁻¹ * (a : A) * g ∈ H := by
        refine (Subgroup.mem_normalizer_iff.mp hgH
          (g⁻¹ * (a : A) * g)).mpr ?_
        simpa only [show g * (g⁻¹ * (a : A) * g) * g⁻¹ = (a : A) by group] using haH
      simpa [gb] using hh
    refine Subgroup.mem_map.mpr ⟨π (gb⁻¹ * a * gb), Subgroup.mem_map_of_mem π hpre, ?_⟩
    change MulAut.conj ((QuotientGroup.mk' P) gb) (π (gb⁻¹ * a * gb)) =
      (QuotientGroup.mk' P) a
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
    change π gb * ((π gb)⁻¹ * π a * π gb) * (π gb)⁻¹ = π a
    group

theorem ggRCS_map_conj_eq_of_mem {A : Type} [Group A] {H : Subgroup A} {g : A} (hg : g ∈ H) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [MulAut.conj_apply] using H.mul_mem (H.mul_mem hg hh) (H.inv_mem hg)
  · intro hx
    refine ⟨g⁻¹ * x * g, H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg, ?_⟩
    change (MulAut.conj g) (g⁻¹ * x * g) = x
    rw [MulAut.conj_apply]
    group

theorem ggRCS_map_conj_eq_of_mem_normalizer {A : Type} [Group A] {H : Subgroup A} {g : A}
    (hg : g ∈ Subgroup.normalizer (H : Set A)) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.mp hg h).mp hh
  · intro hx
    refine ⟨g⁻¹ * x * g, (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * x * g)).mpr ?_, ?_⟩
    · simpa only [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] using hx
    · change (MulAut.conj g) (g⁻¹ * x * g) = x
      rw [MulAut.conj_apply]
      group

noncomputable def ggRCSconjAut {A : Type} [Group A] {H : Subgroup A} {g : A}
    (hm : H.map (MulAut.conj g).toMonoidHom = H) : MulAut ↥H :=
  (H.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
    (MulEquiv.subgroupCongr hm)

theorem ggRCSconjAut_apply {A : Type} [Group A] {H : Subgroup A} {g : A}
    (hm : H.map (MulAut.conj g).toMonoidHom = H) (x : H) :
    ((ggRCSconjAut hm x : H) : A) = g * (x : A) * g⁻¹ := by
  simp only [ggRCSconjAut, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    Subgroup.equivMapOfInjective, MulAut.conj_apply]
  rfl

theorem ggRCSconjAut_inv_apply {A : Type} [Group A] {H : Subgroup A} {g : A}
    (hm : H.map (MulAut.conj g).toMonoidHom = H) (x : H) :
    (((ggRCSconjAut hm)⁻¹ x : H) : A) = g⁻¹ * (x : A) * g := by
  have h := ggRCSconjAut_apply hm ((ggRCSconjAut hm)⁻¹ x)
  have hx : ((ggRCSconjAut hm) ((ggRCSconjAut hm)⁻¹ x) : H) = x :=
    MulEquiv.apply_symm_apply _ _
  rw [hx] at h
  rw [h]
  group

theorem ggRCSconjAut_pCore_map {A : Type} [Group A] {H : Subgroup A} {g : A} (p : ℕ)
    (hm : H.map (MulAut.conj g).toMonoidHom = H) :
    (CFSG.pCore p ↥H).map (ggRCSconjAut hm).toMonoidHom = CFSG.pCore p ↥H :=
  (Subgroup.characteristic_iff_map_eq.mp
    (CFSG.pCore_characteristic (G := ↥H) (p := p))) (ggRCSconjAut hm)

end Generic

section Inputs

theorem ggRCSSix_false_of_y {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} {E : Subgroup G} {r : G} {K S : Subgroup (GGRCSNbar r)}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (hSch : ∀ P : Subgroup G, P ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) → ⁅P, P⁆ = P →
      P ≤ ggG0 p B x L D J)
    (hch : GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r)
    (hset : GGRCSAutKSetting p (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K S)
    [((ggRCSU (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K).subgroupOf
        (ggRCSImg r E ⊔ K)).Normal]
    (hsimple : IsSimpleGroup ↥(CFSG.generalizedFitting
      (ggRCSWt (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K)))
    (hcomp : ∃ C : Subgroup ↥(ggRCSHK (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K),
      CFSG.Open.IsComponentOf C ⊤)
    (hrig : ∀ C : Subgroup ↥(ggRCSHK (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K),
      CFSG.Open.IsComponentOf C ⊤ →
      ∀ α : MulAut ↥(CFSG.generalizedFitting
          (ggRCSWt (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K)),
        (∀ c ∈ C, α ⟨c.1, (Subgroup.mem_inf.mp c.2).2⟩ = ⟨c.1, (Subgroup.mem_inf.mp c.2).2⟩) →
          α = 1)
    {y : G} (hyr : y ∈ Subgroup.centralizer ({r} : Set G)) (hy3 : orderOf y = 3)
    (hyM : Subgroup.centralizer ({y} : Set G) ≤ ggM p B x L D J)
    {J₁ : Subgroup G} (hJ₁y : J₁ ≤ Subgroup.centralizer ({y} : Set G))
    (hJ₁ : ∀ C : Subgroup (GGInvolCentBar (ggG0 p B x L D J) r), CFSG.Open.IsComponentOf C ⊤ →
      C ≤ (J₁.subgroupOf (Subgroup.centralizer ({r} : Set G) ⊓ ggG0 p B x L D J)).map
        (QuotientGroup.mk' (CFSG.Open.pCore 2
          ↥(Subgroup.centralizer ({r} : Set G) ⊓ ggG0 p B x L D J)))) :
    False := by
  classical
  let N : Subgroup G := Subgroup.centralizer ({r} : Set G)
  let P : Subgroup ↥N := CFSG.Assembly.pCore 2 ↥N
  let V : Subgroup (GGRCSNbar r) := ggRCSImg r (ggM p B x L D J)
  have hV : V = ggRCSImg r (ggM p B x L D J) := rfl
  let Eb : Subgroup (GGRCSNbar r) := ggRCSImg r E
  have hEb : Eb = ggRCSImg r E := rfl
  let Y : Subgroup (GGRCSNbar r) := ggRCSImg r (ggG0 p B x L D J)
  have hY : Y = ggRCSImg r (ggG0 p B x L D J) := rfl
  let A₀ : Subgroup G := N ⊓ ggG0 p B x L D J
  have hA : A₀ = N ⊓ ggG0 p B x L D J := rfl
  let Xbar := GGInvolCentBar (ggG0 p B x L D J) r
  have hX : Xbar = GGInvolCentBar (ggG0 p B x L D J) r := rfl
  let ybar : GGRCSNbar r := QuotientGroup.mk ⟨y, hyr⟩
  have hyb : ybar = QuotientGroup.mk ⟨y, hyr⟩ := rfl
  obtain ⟨hKcomp, hKV, hEK, hSK, hQ⟩ := hset
  have hEcomm : ∀ a b : ↥(E.subgroupOf N), a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    simpa only [Subgroup.coe_mul] using congrArg (fun z : ↥E => (z : G))
      (hch.2.1.1.is_comm.comm
        ⟨(a.1 : G), Subgroup.mem_subgroupOf.mp a.2⟩
        ⟨(b.1 : G), Subgroup.mem_subgroupOf.mp b.2⟩)
  have hEsFull : Group.IsSolvable ↥(ggRCSImg r E) :=
    ggRCS_isSolvable_map_of_comm (QuotientGroup.mk' (CFSG.pCore 2 ↥N)) hEcomm
  have hEs : Group.IsSolvable ↥Eb := by
    rw [hEb]
    exact hEsFull
  have hEM : E ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) :=
    hch.1.trans hctx.2.2.2.2.2.2.1.1
  have hEVFull : ggRCSImg r E ≤ ggRCSImg r (ggM p B x L D J) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono N hEM)
  have hEV : Eb ≤ V := by
    rw [hEb, hV]
    exact hEVFull
  obtain ⟨C, hC⟩ := hcomp
  obtain ⟨Dl, hDlcomp, hDlmap⟩ :=
    ggRCS_hk_component_lift (X := GGRCSNbar r) (V := V) (E := Eb) (K := K)
      hEs hEV (by rw [hEb]; exact hEK) hC
  let D' : Subgroup (GGRCSNbar r) := Dl.map (K ⊓ V).subtype
  have hD'V : D' ≤ V := (Subgroup.map_subtype_le Dl).trans inf_le_right
  have hD'compV : CFSG.Open.IsComponentOf (D'.subgroupOf V) ⊤ :=
    (ggRCS_component_inf_lift hKcomp.2 hDlcomp).1
  have hD'compV' : CFSG.Open.IsComponentOf ((D'.subgroupOf V).map V.subtype) V :=
    ggRCS_isComponentOf_map_subtype hD'compV
  have hD'Y' : (D'.subgroupOf V).map V.subtype ≤ Y :=
    ggRCS_component_le_map_of_schreier le_rfl hSch hD'compV'
  have hD'Y : D' ≤ Y := by
    rwa [Subgroup.map_subgroupOf_eq_of_le hD'V] at hD'Y'
  have hYV : Y ≤ V := by
    rw [hY, hV]
    exact Subgroup.map_mono (Subgroup.comap_mono (Subgroup.le_normalizer (H :=
      ggG0 p B x L D J)))
  have hD'compY : CFSG.Open.IsComponentOf (D'.subgroupOf Y) ⊤ := by
    have h := ggRCS_isComponentOf_subgroupOf hD'compV' hD'Y' hYV
    rwa [Subgroup.map_subgroupOf_eq_of_le hD'V] at h
  obtain ⟨σ, hσsurj, hσker, hσformula⟩ :=
    ggRCS_kv_sigma_bar_exists (G₀ := ggG0 p B x L D J) (r := r)
  have hσsol : Group.IsSolvable ↥σ.ker := by
    haveI : Group.IsNilpotent ↥σ.ker := hσker.isNilpotent
    exact IsNilpotent.to_isSolvable
  have hD'compX : CFSG.Open.IsComponentOf ((D'.subgroupOf Y).map σ) ⊤ :=
    (ggRCS_component_map_solvable_ker σ hσsurj hσsol hD'compY).1
  have hD'J : (D'.subgroupOf Y).map σ ≤
      (J₁.subgroupOf A₀).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥A₀)) :=
    hJ₁ ((D'.subgroupOf Y).map σ) hD'compX
  have hyM' : y ∈ ggM p B x L D J :=
    hyM (by rw [Subgroup.mem_centralizer_singleton_iff])
  have hyN : y ∈ N := hyr
  have hA₀conj : A₀.map (MulAut.conj y).toMonoidHom = A₀ :=
    ggRCS_map_conj_eq_of_mem_normalizer (by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      rw [Subgroup.mem_inf, Subgroup.mem_inf]
      constructor
      · rintro ⟨hN, hG⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hyN) h).mp hN,
          (Subgroup.mem_normalizer_iff.mp hyM' h).mp hG⟩
      · rintro ⟨hN, hG⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hyN) h).mpr hN,
          (Subgroup.mem_normalizer_iff.mp hyM' h).mpr hG⟩)
  have hybarV : ybar ∈ V := by
    rw [hV]
    refine Subgroup.mem_map.mpr ⟨⟨y, hyN⟩, Subgroup.mem_subgroupOf.mpr hyM', ?_⟩
    rw [hyb]
    rfl
  have hVA : V.map (MulAut.conj ybar).toMonoidHom = V :=
    ggRCS_map_conj_eq_of_mem hybarV
  have hybar_eq : (QuotientGroup.mk' (CFSG.pCore 2 ↥N) ⟨y, hyN⟩) = ybar := by
    rw [hyb]
    rfl
  have hYA : Y.map (MulAut.conj ybar).toMonoidHom = Y := by
    rw [hY]
    rw [← hybar_eq]
    exact ggRCSImg_conj_eq (N := N) (H := ggG0 p B x L D J) (g := y) hyN hyM' 
  let Esub : Subgroup ↥Y := D'.subgroupOf Y
  let αY : MulAut ↥Y := ggRCSconjAut hYA
  let gb : ↥N := ⟨y, hyN⟩
  have hσ_conj : ∀ xv : ↥Y, xv ∈ Esub → σ (αY xv) = σ xv := by
    intro xv hxv
    have hxD' : (xv : GGRCSNbar r) ∈ D' := Subgroup.mem_subgroupOf.mp hxv
    have hxY : (xv : GGRCSNbar r) ∈ Y := xv.2
    have hxY' : (xv : GGRCSNbar r) ∈
        ((ggG0 p B x L D J).subgroupOf N).map (QuotientGroup.mk' P) := by
      simpa only [hY, ggRCSImg] using hxY
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hxY'
    let aA : ↥A₀ := ⟨a.1, ⟨a.2, Subgroup.mem_subgroupOf.mp ha⟩⟩
    have hσx : σ xv = (QuotientGroup.mk' (CFSG.pCore 2 ↥A₀)) aA := by
      have hx' : xv = ⟨(QuotientGroup.mk' P) a, Subgroup.mem_map_of_mem _ ha⟩ :=
        Subtype.ext hax.symm
      rw [hx']
      simpa only [P, aA] using hσformula aA
    let b : ↥N := gb * a * gb⁻¹
    have hbG : b ∈ (ggG0 p B x L D J).subgroupOf N := by
      rw [Subgroup.mem_subgroupOf]
      have haG : (a : G) ∈ ggG0 p B x L D J := Subgroup.mem_subgroupOf.mp ha
      have hh : y * (a : G) * y⁻¹ ∈ ggG0 p B x L D J :=
        (Subgroup.mem_normalizer_iff.mp hyM' (a : G)).mp haG
      rw [show (b : G) = y * (a : G) * y⁻¹ from rfl]
      exact hh
    let bA : ↥A₀ := ⟨b.1, ⟨b.2, Subgroup.mem_subgroupOf.mp hbG⟩⟩
    have hαx : αY xv = ⟨(QuotientGroup.mk' P) b, Subgroup.mem_map_of_mem _ hbG⟩ := by
      apply Subtype.ext
      rw [ggRCSconjAut_apply]
      rw [← hax, ← hybar_eq]
      change (QuotientGroup.mk' P) gb * (QuotientGroup.mk' P) a *
          ((QuotientGroup.mk' P) gb)⁻¹ = (QuotientGroup.mk' P) b
      rw [show b = gb * a * gb⁻¹ from rfl, map_mul, map_mul, map_inv]
    have hσx' : σ (αY xv) = (QuotientGroup.mk' (CFSG.pCore 2 ↥A₀)) bA := by
      rw [hαx]
      simpa only [P, bA] using hσformula bA
    have hσx_mem : σ xv ∈ Esub.map σ := Subgroup.mem_map_of_mem σ hxv
    have hJx : σ xv ∈ (J₁.subgroupOf A₀).map (QuotientGroup.mk' (CFSG.pCore 2 ↥A₀)) :=
      hD'J hσx_mem
    obtain ⟨j, hjJ, hjmk⟩ := Subgroup.mem_map.mp hJx
    have hjeq : (QuotientGroup.mk' (CFSG.pCore 2 ↥A₀)) j =
        (QuotientGroup.mk' (CFSG.pCore 2 ↥A₀)) aA := by
      rw [hjmk, hσx]
    have ho : j⁻¹ * aA ∈ CFSG.pCore 2 ↥A₀ := QuotientGroup.eq.mp hjeq
    let o : ↥A₀ := j⁻¹ * aA
    have ho_mem : o ∈ CFSG.pCore 2 ↥A₀ := ho
    have haA_decomp : aA = j * o := by
      apply Subtype.ext
      change (aA : G) = (j : G) * ((j : G)⁻¹ * (aA : G))
      group
    have hjJ' : j.1 ∈ J₁ := Subgroup.mem_subgroupOf.mp hjJ
    have hjy : y * (j : G) = (j : G) * y :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hJ₁y hjJ')).symm
    let o' : ↥A₀ := ggRCSconjAut hA₀conj o
    have ho'_coe : (o' : G) = y * (o : G) * y⁻¹ := ggRCSconjAut_apply hA₀conj o
    have ho'_mem : o' ∈ CFSG.pCore 2 ↥A₀ := by
      change (ggRCSconjAut hA₀conj) o ∈ CFSG.pCore 2 ↥A₀
      rw [← ggRCSconjAut_pCore_map 2 hA₀conj]
      exact Subgroup.mem_map_of_mem _ ho_mem
    have hbA_eq : bA = j * o' := by
      apply Subtype.ext
      change (bA : G) = (j : G) * (o' : G)
      have hbA_coe : (bA : G) = y * (aA : G) * y⁻¹ := rfl
      rw [hbA_coe, haA_decomp]
      calc y * ((j : G) * (o : G)) * y⁻¹
          = (y * (j : G) * y⁻¹) * (y * (o : G) * y⁻¹) := by group
        _ = (j : G) * (y * (o : G) * y⁻¹) := by
            rw [show y * (j : G) * y⁻¹ = (j : G) by rw [hjy]; group]
    have hmem : bA⁻¹ * aA ∈ CFSG.pCore 2 ↥A₀ := by
      rw [hbA_eq, haA_decomp]
      have hcalc : ((j * o')⁻¹ * (j * o) : ↥A₀) = o'⁻¹ * o := by
        apply Subtype.ext
        group
      rw [hcalc]
      exact (CFSG.pCore 2 ↥A₀).mul_mem ((CFSG.pCore 2 ↥A₀).inv_mem ho'_mem) ho_mem
    have hclass : (QuotientGroup.mk' (CFSG.pCore 2 ↥A₀)) bA =
        (QuotientGroup.mk' (CFSG.pCore 2 ↥A₀)) aA :=
      QuotientGroup.eq.mpr hmem
    rw [hσx', hσx, hclass]
  have hEsub_comp : CFSG.Open.IsComponentOf Esub ⊤ := hD'compY
  have hEsub''_comp : CFSG.Open.IsComponentOf (Esub.map αY.toMonoidHom) ⊤ :=
    ggRCS_isComponentOf_map_mulAut αY hEsub_comp
  have hmap_eq : (Esub.map αY.toMonoidHom).map σ = Esub.map σ := by
    rw [Subgroup.map_map]
    apply le_antisymm
    · rintro z ⟨x, hx, rfl⟩
      exact Subgroup.mem_map.mpr ⟨x, hx, (hσ_conj x hx).symm⟩
    · rintro z ⟨x, hx, rfl⟩
      exact Subgroup.mem_map.mpr ⟨x, hx, hσ_conj x hx⟩
  have hEeq : Esub = Esub.map αY.toMonoidHom :=
    (ggRCS_map_injOn_components_of_solvable_ker σ hσsurj hσsol)
      hEsub_comp hEsub''_comp hmap_eq.symm
  have hconjD'_le : D'.map (MulAut.conj ybar).toMonoidHom ≤ D' := by
    rintro z ⟨d, hd, rfl⟩
    have hdY : d ∈ Y := hD'Y hd
    have hmemE : (⟨d, hdY⟩ : ↥Y) ∈ Esub := Subgroup.mem_subgroupOf.mpr hd
    have hmemE' : αY ⟨d, hdY⟩ ∈ Esub.map αY.toMonoidHom :=
      Subgroup.mem_map_of_mem αY.toMonoidHom hmemE
    rw [← hEeq] at hmemE'
    have hmemD : (αY ⟨d, hdY⟩ : ↥Y).1 ∈ D' := Subgroup.mem_subgroupOf.mp hmemE'
    rwa [ggRCSconjAut_apply] at hmemD
  have hEinva : Esub.map αY⁻¹.toMonoidHom = Esub := by
    have h := congrArg (Subgroup.map αY⁻¹.toMonoidHom) hEeq
    rw [Subgroup.map_map] at h
    have hid : αY⁻¹.toMonoidHom.comp αY.toMonoidHom = MonoidHom.id (↥Y) := by
      ext z
      exact congrArg Subtype.val (MulEquiv.symm_apply_apply αY z)
    rw [hid, Subgroup.map_id] at h
    exact h
  have hconjD'_ge : D' ≤ D'.map (MulAut.conj ybar).toMonoidHom := by
    intro d hd
    have hdY : d ∈ Y := hD'Y hd
    have hmemE : (⟨d, hdY⟩ : ↥Y) ∈ Esub := Subgroup.mem_subgroupOf.mpr hd
    have hpre : αY⁻¹ ⟨d, hdY⟩ ∈ Esub := by
      have hmem : αY⁻¹ ⟨d, hdY⟩ ∈ Esub.map αY⁻¹.toMonoidHom :=
        Subgroup.mem_map_of_mem αY⁻¹.toMonoidHom hmemE
      rwa [hEinva] at hmem
    have hpreD : (αY⁻¹ ⟨d, hdY⟩ : ↥Y).1 ∈ D' := Subgroup.mem_subgroupOf.mp hpre
    have hpre_coe : (αY⁻¹ ⟨d, hdY⟩ : ↥Y).1 = ybar⁻¹ * d * ybar :=
      ggRCSconjAut_inv_apply hYA ⟨d, hdY⟩
    refine Subgroup.mem_map.mpr ⟨(αY⁻¹ ⟨d, hdY⟩ : ↥Y).1, hpreD, ?_⟩
    rw [hpre_coe]
    change ybar * (ybar⁻¹ * d * ybar) * ybar⁻¹ = d
    group
  have hconjD' : D'.map (MulAut.conj ybar).toMonoidHom = D' :=
    le_antisymm hconjD'_le hconjD'_ge
  have hD'q : CFSG.Open.IsQuasisimple ↥D' :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (Subgroup.subgroupOfEquivOfLe hD'V).symm hD'compV.2.2
  let βD : MulAut ↥D' := ggRCSconjAut hconjD'
  let σD : ↥D' →* Xbar := σ.comp (Subgroup.inclusion hD'Y)
  have hσDker : IsPGroup 2 ↥σD.ker := by
    have hle : (σD.ker).map (Subgroup.inclusion hD'Y) ≤ σ.ker := by
      rintro z ⟨d, hd, rfl⟩
      exact hd
    have hmap2 : IsPGroup 2 ↥((σD.ker).map (Subgroup.inclusion hD'Y)) :=
      IsPGroup.to_le hσker hle
    exact IsPGroup.of_equiv hmap2
      ((σD.ker).equivMapOfInjective (Subgroup.inclusion hD'Y)
        (Subgroup.inclusion_injective hD'Y)).symm
  have hσDsol : Group.IsSolvable ↥σD.ker := by
    haveI : Group.IsNilpotent ↥σD.ker := hσDker.isNilpotent
    exact IsNilpotent.to_isSolvable
  have hstep3aux : ∀ d : ↥D', d⁻¹ * βD d ∈ Subgroup.center ↥D' := by
    intro d
    let z : ↥D' := ⟨ybar * (d : GGRCSNbar r) * ybar⁻¹ * (d : GGRCSNbar r)⁻¹,
      D'.mul_mem (hconjD'_le (Subgroup.mem_map.mpr ⟨(d : GGRCSNbar r), d.2, rfl⟩))
        (D'.inv_mem d.2)⟩
    have hzker : z ∈ σD.ker := by
      rw [MonoidHom.mem_ker]
      have hdY : (d : GGRCSNbar r) ∈ Y := hD'Y d.2
      let x : ↥Y := ⟨d.1, hdY⟩
      have hxE : x ∈ Esub := Subgroup.mem_subgroupOf.mpr d.2
      have hσeq : σ (αY x) = σ x := hσ_conj x hxE
      have hprod : (Subgroup.inclusion hD'Y z : ↥Y) = αY x * x⁻¹ := by
        apply Subtype.ext
        change (z : GGRCSNbar r) =
          ((αY x : ↥Y) : GGRCSNbar r) * ((x : ↥Y) : GGRCSNbar r)⁻¹
        rw [ggRCSconjAut_apply]
      change σ ((Subgroup.inclusion hD'Y) z) = 1
      rw [hprod, map_mul, map_inv, hσeq]
      simp
    have hzcent : z ∈ Subgroup.center ↥D' :=
      ggRCS_solvable_normal_le_center hD'q (W := σD.ker) hσDsol hzker
    have hz : (z : GGRCSNbar r) = ybar * (d : GGRCSNbar r) * ybar⁻¹ * (d : GGRCSNbar r)⁻¹ :=
      rfl
    have hβcoe : ((βD d : ↥D') : GGRCSNbar r) = ybar * (d : GGRCSNbar r) * ybar⁻¹ :=
      ggRCSconjAut_apply hconjD' d
    have hconjmem : d⁻¹ * βD d ∈ Subgroup.center ↥D' := by
      have hconj := (inferInstance : (Subgroup.center ↥D').Normal).conj_mem' z hzcent d
      have hval : (d⁻¹ : ↥D') * z * d = d⁻¹ * βD d := by
        apply Subtype.ext
        change (d : GGRCSNbar r)⁻¹ * (z : GGRCSNbar r) * (d : GGRCSNbar r) =
          (d : GGRCSNbar r)⁻¹ * ((βD d : ↥D') : GGRCSNbar r)
        rw [hz, hβcoe]
        group
      rwa [hval] at hconj
    exact hconjmem
  haveI : Group.IsPerfect ↥D' := ⟨hD'q.1⟩
  have hβD : βD = 1 :=
    CFSG.ComponentClassification.CentralCover.eq_one_of_forall_inv_mul_mem_center βD hstep3aux
  have hstep3 : ∀ d ∈ D', ybar * d * ybar⁻¹ = d := by
    intro d hd
    have hβ : βD ⟨d, hd⟩ = ⟨d, hd⟩ := by rw [hβD]; rfl
    have hcoe : ((βD ⟨d, hd⟩ : ↥D') : GGRCSNbar r) = ybar * d * ybar⁻¹ :=
      ggRCSconjAut_apply hconjD' ⟨d, hd⟩
    rw [hβ] at hcoe
    exact hcoe.symm
  have hD'K : D' ≤ K := (Subgroup.map_subtype_le Dl).trans inf_le_left
  have hstep4 : K.map (MulAut.conj ybar).toMonoidHom = K := by
    by_contra hne
    have hK'open : CFSG.Open.IsComponentOf (K.map (MulAut.conj ybar).toMonoidHom) ⊤ :=
      ggRCS_isComponentOf_map_mulAut (MulAut.conj ybar) ((CFSG.isComponent_iff_open K).mp hKcomp)
    have hK'nat : CFSG.IsComponent (K.map (MulAut.conj ybar).toMonoidHom) :=
      (CFSG.isComponent_iff_open _).mpr hK'open
    have hcommK : ⁅K, K.map (MulAut.conj ybar).toMonoidHom⁆ = ⊥ := by
      rcases CFSG.LocalCores.distinct_components_commute hKcomp hK'nat with h | h
      · exact absurd h.symm hne
      · exact h
    have hD'K' : D' ≤ K.map (MulAut.conj ybar).toMonoidHom := by
      intro d hd
      refine Subgroup.mem_map.mpr ⟨d, hD'K hd, ?_⟩
      change ybar * d * ybar⁻¹ = d
      exact hstep3 d hd
    have hself : ⁅D', D'⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hle : K ≤ Subgroup.centralizer (K.map (MulAut.conj ybar).toMonoidHom) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommK
      exact Subgroup.mem_centralizer_iff.mp (hle (hD'K ha)) b (hD'K' hb)
    haveI : Group.IsPerfect ↥D' := ⟨hD'q.1⟩
    have hD'perf : ⁅D', D'⁆ = D' := Subgroup.isPerfect_iff.mp inferInstance
    rw [hD'perf] at hself
    haveI : Nontrivial ↥D' := nontrivial_of_open_isQuasisimple hD'q
    exact ((Subgroup.nontrivial_iff_ne_bot D').mp inferInstance) hself
  have hstep5 : K ≤ Subgroup.centralizer ({ybar} : Set (GGRCSNbar r)) := by
    haveI hKperfect : Group.IsPerfect ↥K := hKcomp.1.1
    let W := ggRCSWt V Eb K
    let πW : ↥(Eb ⊔ K) →* W :=
      QuotientGroup.mk' ((ggRCSU V Eb K).subgroupOf (Eb ⊔ K))
    let Cmap : Subgroup W := C.map (ggRCSHK V Eb K).subtype
    have hDlmap'' : ((D'.subgroupOf (Eb ⊔ K)).map πW) = Cmap := hDlmap
    let Kbar : Subgroup W := (K.subgroupOf (Eb ⊔ K)).map πW
    let Fstar : Subgroup W := CFSG.generalizedFitting W
    haveI : IsSimpleGroup ↥Fstar := hsimple
    have hπWsurj : Function.Surjective πW := QuotientGroup.mk'_surjective _
    have hKbar_normal : Kbar.Normal := by
      have hKn : (K.subgroupOf (Eb ⊔ K)).Normal := by
        rw [Subgroup.normal_subgroupOf_iff (le_sup_right : K ≤ Eb ⊔ K)]
        intro h k hh hk
        have hkN : k ∈ Subgroup.normalizer (K : Set (GGRCSNbar r)) :=
          (sup_le hEK Subgroup.le_normalizer) hk
        exact (Subgroup.mem_normalizer_iff.mp hkN h).mp hh
      exact hKn.map πW hπWsurj
    let πK : ↥K →* W := πW.comp (Subgroup.inclusion (le_sup_right : K ≤ Eb ⊔ K))
    have hπK_range : πK.range = Kbar := by
      rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    have hKbar_perf : ⁅Kbar, Kbar⁆ = Kbar := by
      haveI hKperfect : Group.IsPerfect ↥K := hKcomp.1.1
      have hKperf : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ :=
        Group.IsPerfect.commutator_eq_top
      calc ⁅Kbar, Kbar⁆ = ⁅πK.range, πK.range⁆ := by rw [hπK_range]
        _ = ⁅(⊤ : Subgroup ↥K).map πK, (⊤ : Subgroup ↥K).map πK⁆ := by
            rw [MonoidHom.range_eq_map]
        _ = (⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆).map πK :=
            (Subgroup.map_commutator _ _ _).symm
        _ = (⊤ : Subgroup ↥K).map πK := by rw [hKperf]
        _ = Kbar := by rw [← MonoidHom.range_eq_map, hπK_range]
    have hEab : ∀ a ∈ Eb, ∀ b ∈ Eb, Commute a b := by
      intro a ha b hb
      have ha' : a ∈ (E.subgroupOf N).map (QuotientGroup.mk' P) := by
        simpa only [hEb, ggRCSImg] using ha
      have hb' : b ∈ (E.subgroupOf N).map (QuotientGroup.mk' P) := by
        simpa only [hEb, ggRCSImg] using hb
      exact ggRCS_commute_of_mem_map _ hEcomm ha' hb'
    have hKbar_le_F : Kbar ≤ Fstar :=
      ggRCS_perfect_le_generalizedFitting hKcomp hEK hEab Kbar hKbar_perf
    have hKbar_ne : Kbar ≠ ⊥ := by
      intro hbot
      have hker : K.subgroupOf (Eb ⊔ K) ≤ πW.ker := by
        rw [Subgroup.map_eq_bot_iff] at hbot
        exact hbot
      have hU' : ∀ x : ↥(Eb ⊔ K), πW x = 1 ↔ (x : GGRCSNbar r) ∈ ggRCSU V Eb K := by
        intro x
        change (QuotientGroup.mk' ((ggRCSU V Eb K).subgroupOf (Eb ⊔ K))) x = 1 ↔ _
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      have hKcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
        intro a ha b hb
        have haU : a ∈ ggRCSU V Eb K := by
          have hx : (⟨a, (le_sup_right : K ≤ Eb ⊔ K) ha⟩ : ↥(Eb ⊔ K)) ∈ πW.ker :=
            hker (Subgroup.mem_subgroupOf.mpr ha)
          exact (hU' _).mp (MonoidHom.mem_ker.mp hx)
        exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp haU).2 b hb).symm
      have hKcA : CFSG.Assembly.IsComponentOf K ⊤ :=
        (CFSG.Assembly.isComponentOf_iff_open).mpr ((CFSG.isComponent_iff_open K).mp hKcomp)
      exact ggComponent_not_commute hKcA hKcomm
    have hKbar_eq_F : Kbar = Fstar := by
      have hnorm : (Kbar.subgroupOf Fstar).Normal :=
        hKbar_normal.subgroupOf Fstar
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Kbar.subgroupOf Fstar) with hbot | htop
      · exfalso
        have h := congrArg (Subgroup.map Fstar.subtype) hbot
        rw [Subgroup.map_subgroupOf_eq_of_le hKbar_le_F, Subgroup.map_bot] at h
        exact hKbar_ne h
      · have h := congrArg (Subgroup.map Fstar.subtype) htop
        rw [Subgroup.map_subgroupOf_eq_of_le hKbar_le_F, Subgroup.map_top,
          Subgroup.range_subtype] at h
        exact h
    have hFperf : Group.IsPerfect ↥Fstar := by
      haveI : Group.IsPerfect ↥Kbar := Subgroup.isPerfect_iff.mpr hKbar_perf
      rw [hKbar_eq_F] at this
      exact this
    have hFcenter : Subgroup.center ↥Fstar = ⊥ :=
      ggRCS_center_eq_bot_of_isSimpleGroup_of_isPerfect hFperf
    have hπK_le_F : ∀ k : ↥K, πK k ∈ Fstar := by
      intro k
      have hmem : πK k ∈ Kbar := by
        rw [← hπK_range]
        exact ⟨k, rfl⟩
      rwa [hKbar_eq_F] at hmem
    let φ : ↥K →* ↥Fstar := πK.codRestrict Fstar hπK_le_F
    have hφsurj : Function.Surjective φ := by
      intro x
      have hx : (x : W) ∈ Kbar := by
        rw [hKbar_eq_F]
        exact x.2
      have hx' : (x : W) ∈ πK.range := by rwa [hπK_range]
      obtain ⟨k, hk⟩ := hx'
      exact ⟨k, Subtype.ext hk⟩
    have hker_le : φ.ker ≤ Subgroup.center ↥K := by
      intro k hk
      have hk1 : πK k = 1 := by
        have h := congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
        change (φ k : W) = 1 at h
        simpa only [φ, MonoidHom.codRestrict_apply] using h
      have hkU : (k : GGRCSNbar r) ∈ ggRCSU V Eb K := by
        have h : (Subgroup.inclusion (le_sup_right : K ≤ Eb ⊔ K) k : ↥(Eb ⊔ K)) ∈
            (ggRCSU V Eb K).subgroupOf (Eb ⊔ K) := by
          have h0 : πW (Subgroup.inclusion (le_sup_right : K ≤ Eb ⊔ K) k) = 1 := hk1
          exact (QuotientGroup.eq_one_iff (N := (ggRCSU V Eb K).subgroupOf (Eb ⊔ K)) _).mp h0
        exact Subgroup.mem_subgroupOf.mp h
      rw [Subgroup.mem_center_iff]
      intro b
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hkU).2
        (b : GGRCSNbar r) b.2)
    have hker_ge : Subgroup.center ↥K ≤ φ.ker := by
      intro z hz
      rw [MonoidHom.mem_ker]
      have hzF : φ z ∈ Subgroup.center ↥Fstar := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨k, rfl⟩ := hφsurj y
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz k]
      rw [hFcenter] at hzF
      exact Subgroup.mem_bot.mp hzF
    have hker_eq : φ.ker = Subgroup.center ↥K := le_antisymm hker_le hker_ge
    let e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥Fstar :=
      (QuotientGroup.quotientMulEquivOfEq hker_eq.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)
    have h_e_mk : ∀ k : ↥K,
        e (QuotientGroup.mk' (Subgroup.center ↥K) k) = φ k := by
      intro k
      change (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)
        ((QuotientGroup.quotientMulEquivOfEq hker_eq.symm)
          (QuotientGroup.mk' (Subgroup.center ↥K) k)) = φ k
      rw [QuotientGroup.mk'_apply, QuotientGroup.quotientMulEquivOfEq_mk]
      rfl
    let β : MulAut ↥K := ggRCSconjAut hstep4
    let βbar : MulAut (↥K ⧸ Subgroup.center ↥K) :=
      CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient β
    let α : MulAut ↥Fstar := MulAut.congr e βbar
    have hα_apply : ∀ k : ↥K, α (φ k) = φ (β k) := by
      intro k
      have hk : φ k = e (QuotientGroup.mk' (Subgroup.center ↥K) k) := (h_e_mk k).symm
      rw [hk]
      change (MulAut.congr e βbar) (e (QuotientGroup.mk' (Subgroup.center ↥K) k)) = φ (β k)
      rw [MulAut.congr_apply]
      change e (βbar (e.symm (e (QuotientGroup.mk' (Subgroup.center ↥K) k)))) = φ (β k)
      have hsymm : e.symm (e (QuotientGroup.mk' (Subgroup.center ↥K) k)) =
          QuotientGroup.mk' (Subgroup.center ↥K) k :=
        e.symm_apply_apply _
      have hβbar_eq : βbar (QuotientGroup.mk' (Subgroup.center ↥K) k) =
          QuotientGroup.mk' (Subgroup.center ↥K) (β k) :=
        CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk β k
      rw [hsymm, hβbar_eq]
      exact h_e_mk (β k)
    have hfixC : ∀ c ∈ C,
        α ⟨c.1, (Subgroup.mem_inf.mp c.2).2⟩ = ⟨c.1, (Subgroup.mem_inf.mp c.2).2⟩ := by
      intro c hc
      have hcR : c.1 ∈ Cmap := Subgroup.mem_map_of_mem _ hc
      have hc_mem : c.1 ∈ ((D'.subgroupOf (Eb ⊔ K)).map πW) := hDlmap''.symm ▸ hcR
      obtain ⟨x, hx, hπx⟩ := Subgroup.mem_map.mp hc_mem
      have hxD' : (x : GGRCSNbar r) ∈ D' := Subgroup.mem_subgroupOf.mp hx
      have hxK : (x : GGRCSNbar r) ∈ K := hD'K hxD'
      let k : ↥K := ⟨x.1, hxK⟩
      have hkx : (Subgroup.inclusion (le_sup_right : K ≤ Eb ⊔ K) k : ↥(Eb ⊔ K)) = x :=
        Subtype.ext rfl
      have hφk : φ k = ⟨c.1, (Subgroup.mem_inf.mp c.2).2⟩ := by
        apply Subtype.ext
        change πW (Subgroup.inclusion (le_sup_right : K ≤ Eb ⊔ K) k) = c.1
        rw [hkx]
        exact hπx
      have hβk : β k = k := by
        apply Subtype.ext
        rw [ggRCSconjAut_apply]
        exact hstep3 k.1 hxD'
      rw [← hφk, hα_apply, hβk, hφk]
    have hα1 : α = 1 := hrig C hC α hfixC
    have hcenterK : ∀ k : ↥K, k⁻¹ * β k ∈ Subgroup.center ↥K := by
      intro k
      have hαeq : α (φ k) = φ k := by rw [hα1]; rfl
      rw [hα_apply] at hαeq
      have hq : (QuotientGroup.mk' (Subgroup.center ↥K)) (β k) =
          (QuotientGroup.mk' (Subgroup.center ↥K)) k := by
        apply e.injective
        rw [h_e_mk, h_e_mk]
        exact hαeq
      have hmk : (QuotientGroup.mk' (Subgroup.center ↥K)) (β k * k⁻¹) = 1 := by
        rw [map_mul, map_inv, hq, mul_inv_cancel]
      have hmem : β k * k⁻¹ ∈ Subgroup.center ↥K :=
        (QuotientGroup.eq_one_iff _).mp hmk
      have hconj := (inferInstance : (Subgroup.center ↥K).Normal).conj_mem' (β k * k⁻¹) hmem k
      have hcalc : k⁻¹ * (β k * k⁻¹) * k = k⁻¹ * β k := by group
      rwa [hcalc] at hconj
    have hβ1 : β = 1 :=
      CFSG.ComponentClassification.CentralCover.eq_one_of_forall_inv_mul_mem_center β hcenterK
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hβk : β ⟨k, hk⟩ = ⟨k, hk⟩ := by rw [hβ1]; rfl
    have hcoe : ((β ⟨k, hk⟩ : ↥K) : GGRCSNbar r) = ybar * k * ybar⁻¹ :=
      ggRCSconjAut_apply hstep4 ⟨k, hk⟩
    rw [hβk] at hcoe
    have hk_eq : (k : GGRCSNbar r) = ybar * k * ybar⁻¹ := hcoe
    calc (k : GGRCSNbar r) * ybar = (ybar * k * ybar⁻¹) * ybar := by
          conv_lhs => rw [hk_eq]
      _ = ybar * k := by
          conv_lhs => rw [mul_assoc, inv_mul_cancel, mul_one]
  have hcent := ggRCS_centralizer_bar_le (M := ggM p B x L D J) (r := r)
    (e := ⟨y, hyr⟩) hy3 hyM
  have hKV' : K ≤ V := by
    rw [hV]
    simpa only [← hyb] using hstep5.trans hcent
  exact hKV hKV'

end Inputs

end CFSG.StandardType
