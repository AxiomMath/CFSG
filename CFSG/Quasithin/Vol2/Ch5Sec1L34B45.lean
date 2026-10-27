module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34B45Swap
public import CFSG.Quasithin.Vol2.Ch5Sec1L34InputsD3
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.H13.B45L34

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
  CFSG.Quasithin.InternalSec
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped IsMulCommutative

theorem isElemAbelian_radP {k : Type} [Field k] [CharP k 2] :
    IsElemAbelian 2 (KGL34P.radP (k := k)) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨b₁, c₁, h₁⟩ := KGL34P.mem_radP.mp a.2
    obtain ⟨b₂, c₂, h₂⟩ := KGL34P.mem_radP.mp b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← h₁, ← h₂, ← map_mul, ← map_mul, KGL34P.rad_mul,
      KGL34P.rad_mul, add_comm b₁, add_comm c₁]
  · obtain ⟨b, c, rfl⟩ := KGL34P.mem_radP.mp hx
    rw [← map_pow, pow_two, KGL34P.rad_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero,
      KGL34P.rad_zero, map_one]

theorem exists_elemSixteen_coatom {X : Type} [Group X] [Finite X] (hX : LieModel X .PSL 3 2 2)
    {S₀ : Subgroup X} (hS : IsSylowTwoOf S₀ ⊤) :
    ∃ R : Subgroup X, R ≤ S₀ ∧ IsElemAbelian 2 R ∧ Nat.card R = 16 ∧
      IsCoatom (Subgroup.normalizer (R : Set X)) ∧
      Subgroup.normalizer (S₀ : Set X) ≤ Subgroup.normalizer (R : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, _, hk, e, he⟩ := exists_mulEquiv_sylow_eq hX hS
  have : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have hS₀ : S₀ = (projUnitriangular 3 k).map e.symm.toMonoidHom := by
    rw [← he, Subgroup.map_map]
    simp
  refine ⟨(KGL34P.radP (k := k)).map e.symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hS₀]
    exact Subgroup.map_mono KGL34P.radP_le_projUnitriangular
  · exact H13.isElemAbelian_map_mulEquiv e.symm isElemAbelian_radP
  · rw [Subgroup.card_map_of_injective e.symm.injective, KGL34P.card_radP hk]
  · rw [← Subgroup.map_equiv_normalizer_eq, KGL34P.normalizer_radP hk]
    exact (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup e.symm) _).mpr
      (isCoatom_projStabilizer_flagSpace (K := k) (n := 3) le_rfl (by norm_num))
  · rw [hS₀, ← Subgroup.map_equiv_normalizer_eq, ← Subgroup.map_equiv_normalizer_eq,
      normalizer_projUnitriangular (K := k) 2, KGL34P.normalizer_radP hk]
    exact Subgroup.map_mono (projUpperTriangular_le_projStabilizer 1)

theorem false_of_isDiagramNontrivial {Γ X : Type} [Group Γ] [Group X] {K T : Subgroup Γ}
    (hTK : T ≤ Subgroup.normalizer (K : Set Γ)) (hS : IsSylowTwoOf (T ⊓ K) K)
    (κ : ↥K →* X) (hκ : Function.Surjective κ) (α : ↥T →* MulAut X)
    (hα : ∀ (t : ↥T) (k : ↥K), α t (κ k) =
      κ ⟨t * k * t⁻¹, (Subgroup.mem_normalizer_iff.mp (hTK t.2) k).mp k.2⟩)
    {R : Subgroup X} (hR : IsCoatom (Subgroup.normalizer (R : Set X)))
    (hRS : ∀ k : ↥K, (k : Γ) ∈ Subgroup.normalizer ((T ⊓ K : Subgroup Γ) : Set Γ) →
      κ k ∈ Subgroup.normalizer (R : Set X))
    (hαR : ∀ t : ↥T, R.map (α t).toMonoidHom = R)
    (hD : E2.IsDiagramNontrivial T K (T ⊓ K)) : False := by
  set P' : Subgroup ↥K := (Subgroup.normalizer (R : Set X)).comap κ with hP'
  set P : Subgroup Γ := P'.map K.subtype with hP
  have hPK : P ≤ K := by
    rintro _ ⟨k, -, rfl⟩
    exact k.2
  have hmemP : ∀ (g : Γ) (hg : g ∈ K), g ∈ P ↔ κ ⟨g, hg⟩ ∈ Subgroup.normalizer (R : Set X) := by
    intro g hg
    constructor
    · rintro ⟨k, hk, hkg⟩
      have : k = ⟨g, hg⟩ := Subtype.ext hkg
      rw [← this]
      exact hk
    · intro h
      exact ⟨⟨g, hg⟩, h, rfl⟩
  have hBP : K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup Γ) : Set Γ) ≤ P := by
    rintro g ⟨hgK, hgN⟩
    exact (hmemP g hgK).mpr (hRS ⟨g, hgK⟩ hgN)
  have hPne : P ≠ K := by
    intro hPK'
    apply hR.1
    rw [eq_top_iff]
    intro x _
    obtain ⟨k, rfl⟩ := hκ x
    have hk : (k : Γ) ∈ P := by
      rw [hPK']
      exact k.2
    exact (hmemP k k.2).mp hk
  have hmax : IsMaxParabolic2 K P := by
    refine ⟨⟨hPK, T ⊓ K, hS, hBP⟩, hPne, fun Q hQ hQK hPQ => ?_⟩
    have hQK' : Q ≤ K := hQ.1
    let M : Subgroup X := (Q.subgroupOf K).map κ
    have hNM : Subgroup.normalizer (R : Set X) ≤ M := by
      intro x hx
      obtain ⟨k, rfl⟩ := hκ x
      have hk : (k : Γ) ∈ P := (hmemP k k.2).mpr hx
      exact ⟨k, hPQ hk, rfl⟩
    rcases hR.le_iff.mp hNM with hMeq | hMeq
    · exfalso
      apply hQK
      apply le_antisymm hQK'
      intro g hg
      have hx : κ ⟨g, hg⟩ ∈ M := by
        rw [hMeq]
        exact Subgroup.mem_top _
      obtain ⟨q, hq, hqg⟩ := hx
      have h1 : q⁻¹ * ⟨g, hg⟩ ∈ P' := by
        show κ (q⁻¹ * ⟨g, hg⟩) ∈ Subgroup.normalizer (R : Set X)
        rw [map_mul, map_inv, hqg, inv_mul_cancel]
        exact Subgroup.one_mem _
      have h2 : ((q⁻¹ * ⟨g, hg⟩ : ↥K) : Γ) ∈ Q := hPQ ⟨_, h1, rfl⟩
      have h3 := Q.mul_mem (show (q : Γ) ∈ Q from hq) h2
      simpa using h3
    · apply le_antisymm _ hPQ
      intro g hg
      have hx : κ ⟨g, hQK' hg⟩ ∈ M := ⟨⟨g, hQK' hg⟩, hg, rfl⟩
      rw [hMeq] at hx
      exact (hmemP g (hQK' hg)).mpr hx
  apply hD P hmax hBP
  have hconj : ∀ t ∈ T, ∀ g ∈ P, t * g * t⁻¹ ∈ P := by
    intro t ht g hg
    have hgK := hPK hg
    have htg : t * g * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hTK ht) g).mp hgK
    refine (hmemP _ htg).mpr ?_
    have h1 := hα ⟨t, ht⟩ ⟨g, hgK⟩
    have h2 : κ ⟨t * g * t⁻¹, htg⟩ = α ⟨t, ht⟩ (κ ⟨g, hgK⟩) := h1.symm
    rw [h2]
    have h3 : κ ⟨g, hgK⟩ ∈ Subgroup.normalizer (R : Set X) := (hmemP g hgK).mp hg
    have h4 : (Subgroup.normalizer (R : Set X)).map (α ⟨t, ht⟩).toMonoidHom =
        Subgroup.normalizer (R : Set X) := by
      rw [Subgroup.map_equiv_normalizer_eq, hαR]
    rw [← h4]
    exact ⟨_, h3, rfl⟩
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => hconj t ht g hg, fun hg => ?_⟩
  have := hconj t⁻¹ (T.inv_mem ht) _ hg
  simpa [mul_assoc] using this


theorem isElemAbelian_map_hom {M N : Type*} [Group M] [Group N] (f : M →* N) {E : Subgroup M}
    (hE : IsElemAbelian 2 E) : IsElemAbelian 2 (E.map f) := CFSG.Open.IsElemAbelian.map hE _

theorem map_normalizerMonoidHom_eq_iff {M : Type*} [Group M] {L : Subgroup M}
    (g : ↥(Subgroup.normalizer (L : Set M))) (A : Subgroup ↥L) :
    A.map (L.normalizerMonoidHom g).toMonoidHom = A ↔
      (g : M) ∈ Subgroup.normalizer ((A.map L.subtype : Subgroup M) : Set M) := by
  have hφ : ∀ a : ↥L, ((L.normalizerMonoidHom g a : ↥L) : M) = g * a * (g : M)⁻¹ :=
    fun _ => rfl
  have hφs : ∀ a : ↥L, (((L.normalizerMonoidHom g).symm a : ↥L) : M) = (g : M)⁻¹ * a * g := by
    intro a
    have h1 := hφ ((L.normalizerMonoidHom g).symm a)
    rw [MulEquiv.apply_symm_apply] at h1
    rw [show (g : M)⁻¹ * a * g = (g : M)⁻¹ * (g * (((L.normalizerMonoidHom g).symm a : ↥L) : M) *
      (g : M)⁻¹) * g from by rw [← h1]]
    group
  constructor
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨L.normalizerMonoidHom g a, ?_, hφ a⟩
      rw [← h]
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a', ha', hxa⟩
      change (a' : M) = g * x * (g : M)⁻¹ at hxa
      have hxL : x ∈ L := by
        have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ g.2) _).mp a'.2
        rw [hxa] at h1
        simpa [mul_assoc] using h1
      refine ⟨⟨x, hxL⟩, ?_, rfl⟩
      have h1 : L.normalizerMonoidHom g ⟨x, hxL⟩ = a' := Subtype.ext (by rw [hφ]; exact hxa.symm)
      rw [← h] at ha'
      obtain ⟨b, hb, hba⟩ := ha'
      rw [← h1] at hba
      have := (L.normalizerMonoidHom g).injective hba
      rwa [← this]
  · intro h
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      have h1 := (Subgroup.mem_normalizer_iff.mp h (b : M)).mp ⟨b, hb, rfl⟩
      obtain ⟨c, hc, hcb⟩ := h1
      change (c : M) = g * b * (g : M)⁻¹ at hcb
      have : c = L.normalizerMonoidHom g b := Subtype.ext (by rw [hφ]; exact hcb)
      show L.normalizerMonoidHom g b ∈ A
      rw [← this]
      exact hc
    · intro ha
      refine ⟨(L.normalizerMonoidHom g).symm a, ?_, MulEquiv.apply_symm_apply _ _⟩
      have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ h) (a : M)).mp ⟨a, ha, rfl⟩
      obtain ⟨c, hc, hca⟩ := h1
      change (c : M) = (g : M)⁻¹ * a * (g : M)⁻¹⁻¹ at hca
      have : c = (L.normalizerMonoidHom g).symm a := by
        apply Subtype.ext
        rw [hφs, hca]
        simp
      rw [← this]
      exact hc

theorem lieModel_psl34_of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : LieModel X .PSL 3 2 2) : LieModel X' .PSL 3 2 2 :=
  CFSG.Blueprint.LieModel.of_mulEquiv e h

theorem center_eq_bot_of_lieModel {X : Type} [Group X] (h : LieModel X .PSL 3 2 2) :
    Subgroup.center X = ⊥ := by
  obtain ⟨k, _, _, hk, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_of_lieModel h
  have hZ := LinearThreeFourOuter.center_projectiveSL_three_eq_bot (k := k) (by norm_num [hk])
  rw [eq_bot_iff]
  intro z hz
  have h1 : e z ∈ Subgroup.center (projectiveSL 3 k) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hz x]
  rw [hZ, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact e.injective (h1.trans e.map_one.symm)

theorem b45L34Fact_holds :
    B45L34Fact := by
  intro Γ _ _ U Y K T Cg _ hI hSQ hL hTY hT hYKT hD
  by_contra hq
  push Not at hq
  have hQ := hI.qsec
  have hU2 : ∀ v : ↥U, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hI.elem v v.2)
  have hV := Bridge.sec_sq_eq_one hU2 (⊤ : Subgroup ↥U) (Cg.subgroupOf U)
  have hHyp := hI.b4Hyp hSQ
  set G := autSec (autOn Y U) ⊤ (Cg.subgroupOf U) with hG
  set L := autSec (autOn K U) ⊤ (Cg.subgroupOf U) with hLdef
  have hGN : G ≤ Subgroup.normalizer (L : Set (MulAut (Sec (⊤ : Subgroup ↥U)
      (Cg.subgroupOf U)))) := B42L2.le_normalizer_of_b4Hyp hHyp
  have eKL : ↥(autOn K U) ≃* ↥L :=
    B5.secEquiv (autOn K U) (le_stabSub_top _) hQ.stabKC hQ.faithful
  have hLL : LieModel ↥L .PSL 3 2 2 := lieModel_psl34_of_mulEquiv eKL hL
  have hZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_lieModel hLL
  have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L)
      .PSL 3 2 2 := by
    have h1 := CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hLL
    obtain ⟨hadm, k, hk, hkf, hcard, ⟨e'⟩⟩ := h1
    exact ⟨hadm, k, hk, hkf, hcard,
      ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e'⟩⟩
  have hYU := hI.normU
  let ι : ↥Y →* ↥(autOn Y U) :=
    ((conjAct U).comp (Subgroup.inclusion hYU)).codRestrict (autOn Y U)
      (fun y => ⟨Subgroup.inclusion hYU y, y.2, rfl⟩)
  let σ := B5.secHom (autOn Y U) (le_stabSub_top _) hQ.stab
  let lamY : ↥Y →* MulAut (Sec (⊤ : Subgroup ↥U) (Cg.subgroupOf U)) := σ.comp ι
  have hlamG : ∀ y : ↥Y, lamY y ∈ G := fun y => by
    rw [hG, ← B5.range_secHom (autOn Y U) (le_stabSub_top _) hQ.stab]
    exact ⟨ι y, rfl⟩
  let κ : ↥K →* MulAut (Sec (⊤ : Subgroup ↥U) (Cg.subgroupOf U)) :=
    lamY.comp (Subgroup.inclusion hI.le)
  have hκr : κ.range = L := by
    have h1 : (ι.comp (Subgroup.inclusion hI.le)).range = (autOn K U).subgroupOf (autOn Y U) := by
      ext x
      rw [MonoidHom.mem_range, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨⟨k, hYU (hI.le k.2)⟩, k.2, rfl⟩
      · rintro ⟨n, hn, hnx⟩
        refine ⟨⟨n, hn⟩, Subtype.ext ?_⟩
        exact hnx
    have h2 := B5.map_secHom_eq_autSec (autOn Y U) (le_stabSub_top _) hQ.stab hI.autOn_le
    rw [← h1] at h2
    rw [hLdef, ← h2, ← MonoidHom.range_comp]
    rfl
  let κL : ↥K →* ↥L := κ.codRestrict L (fun k => by rw [← hκr]; exact ⟨k, rfl⟩)
  have hκL : Function.Surjective κL := by
    intro l
    have : (l : MulAut _) ∈ κ.range := by
      rw [hκr]
      exact l.2
    obtain ⟨k, hk⟩ := this
    exact ⟨k, Subtype.ext hk⟩
  have hTK : T ≤ Subgroup.normalizer (K : Set Γ) := hTY.trans hI.normL
  let lamT : ↥T →* ↥(Subgroup.normalizer (L : Set (MulAut (Sec (⊤ : Subgroup ↥U)
      (Cg.subgroupOf U))))) :=
    (lamY.comp (Subgroup.inclusion hTY)).codRestrict _ (fun t => hGN (hlamG _))
  let α : ↥T →* MulAut ↥L := L.normalizerMonoidHom.comp lamT
  have hαapp : ∀ (t : ↥T) (k : ↥K), α t (κL k) =
      κL ⟨t * k * t⁻¹, (Subgroup.mem_normalizer_iff.mp (hTK t.2) k).mp k.2⟩ := by
    intro t k
    apply Subtype.ext
    show lamY (Subgroup.inclusion hTY t) * lamY (Subgroup.inclusion hI.le k) *
        (lamY (Subgroup.inclusion hTY t))⁻¹ = lamY ⟨t * k * t⁻¹, _⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hTKs : IsSylowTwoOf (T ⊓ K) K := A4.isSylowTwoOf_inf_normal hT hI.le hI.normL
  set Sb : Subgroup ↥L := ((T ⊓ K).subgroupOf K).map κL with hSb
  have hSb : IsSylowTwoOf Sb ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hTKs) κL hκL
  obtain ⟨R, hRS, hRe, hRc, hRco, hNR⟩ := exists_elemSixteen_coatom hLL hSb
  have hTSb : ∀ t : ↥T, Sb.map (α t).toMonoidHom = Sb := by
    intro t
    have hle : ∀ t : ↥T, Sb.map (α t).toMonoidHom ≤ Sb := by
      intro t
      rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      refine ⟨⟨t * k * t⁻¹, (Subgroup.mem_normalizer_iff.mp (hTK t.2) k).mp k.2⟩, ?_,
        (hαapp t k).symm⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hk ⊢
      exact ⟨T.mul_mem (T.mul_mem t.2 hk.1) (T.inv_mem t.2),
        (Subgroup.mem_normalizer_iff.mp (hTK t.2) k).mp k.2⟩
    refine le_antisymm (hle t) ?_
    intro s hs
    refine ⟨α t⁻¹ s, hle t⁻¹ ⟨s, hs, rfl⟩, ?_⟩
    show α t (α t⁻¹ s) = s
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have : Finite (MulAut (Sec (⊤ : Subgroup ↥U) (Cg.subgroupOf U))) :=
    Finite.of_injective (fun g : MulAut (Sec (⊤ : Subgroup ↥U) (Cg.subgroupOf U)) =>
      (g : Sec (⊤ : Subgroup ↥U) (Cg.subgroupOf U) → Sec (⊤ : Subgroup ↥U) (Cg.subgroupOf U)))
      DFunLike.coe_injective
  have hTR : ∀ t : ↥T, R.map (α t).toMonoidHom = R := by
    intro t
    have hg : ((lamT t : ↥(Subgroup.normalizer _)) : MulAut _) ∈ G := hlamG _
    have hgS := (map_normalizerMonoidHom_eq_iff (lamT t) Sb).mp (hTSb t)
    have hSL : IsSylowTwoOf (Sb.map L.subtype) L :=
      CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_map_subtype hSb
    have hQn := mem_normalizer_of_qhatOf_le_two hV hHyp hZ hmodel hq hSL (Subgroup.map_mono hRS)
      (isElemAbelian_map_hom L.subtype hRe)
      (by rw [Subgroup.card_map_of_injective L.subtype_injective, hRc]) hg hgS
    exact (map_normalizerMonoidHom_eq_iff (lamT t) R).mpr hQn
  have hRS' : ∀ k : ↥K, (k : Γ) ∈ Subgroup.normalizer ((T ⊓ K : Subgroup Γ) : Set Γ) →
      κL k ∈ Subgroup.normalizer (R : Set ↥L) := by
    intro k hk
    apply hNR
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨k * x * k⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx ⊢
      exact (Subgroup.mem_normalizer_iff.mp hk x).mp hx
    · rintro ⟨x, hx, hxs⟩
      refine ⟨k⁻¹ * x * k, ?_, ?_⟩
      · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx ⊢
        have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hk) x).mp hx
        simpa [mul_assoc] using h1
      · show κL (k⁻¹ * x * k) = s
        have hxs' : κL x = κL k * s * (κL k)⁻¹ := hxs
        rw [map_mul, map_mul, map_inv, hxs']
        group
  exact false_of_isDiagramNontrivial hTK hTKs κL hκL α hαapp hRco hRS' hTR hD

end CFSG.Quasithin.H13.B45L34
