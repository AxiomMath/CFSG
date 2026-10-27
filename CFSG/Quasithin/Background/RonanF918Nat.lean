module

public import CFSG.Quasithin.Background.RonanF918FF
public import CFSG.Quasithin.Background.B5Sec
public import CFSG.Quasithin.Background.B4ModelsIso

public section

namespace CFSG.Quasithin.RonanF918

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

section Transport

theorem realizesVia_transport {V V' : Type*} [CommGroup V] [CommGroup V'] {D : FFModel}
    {H : Subgroup (MulAut V)} {H' : Subgroup (MulAut V')} {U Z : Subgroup V}
    {π : D.Gam →* ↥H} (hD : D.RealizesVia H U Z π)
    (ρ : ↥U →* V') (hρs : Function.Surjective ρ) (hρk : ∀ u : ↥U, ρ u = 1 ↔ (u : V) ∈ Z)
    (τ : ↥H →* ↥H') (hτs : Function.Surjective τ)
    (hτρ : ∀ (x : ↥H) (u : ↥U) (hu : (x : MulAut V) (u : V) ∈ U),
      ((τ x : ↥H') : MulAut V') (ρ u) = ρ ⟨(x : MulAut V) (u : V), hu⟩) :
    D.RealizesVia H' (⊤ : Subgroup V') (⊥ : Subgroup V') (τ.comp π) := by
  obtain ⟨hπs, hZU, hkerle, hUinv, hZinv, hsec, hkinv, β, hβs, hβk, hβe⟩ := hD
  have hker : ρ.ker ≤ β.ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    exact (hβk u).mpr ((hρk u).mp hu)
  let ρe : ↥U ⧸ ρ.ker ≃* V' := QuotientGroup.quotientKerEquivOfSurjective ρ hρs
  let β₁ : V' →* ↥D.sec ⧸ D.ker.subgroupOf D.sec :=
    (QuotientGroup.lift ρ.ker β hker).comp ρe.symm.toMonoidHom
  have hβ₁ : ∀ u : ↥U, β₁ (ρ u) = β u := by
    intro u
    have h1 : ρe.symm (ρ u) = QuotientGroup.mk u := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show (QuotientGroup.lift ρ.ker β hker) (ρe.symm (ρ u)) = β u
    rw [h1]
    rfl
  refine ⟨(hτs.comp hπs), bot_le, hkerle, fun _ _ _ => trivial, fun h z hz => ?_, hsec, hkinv,
    β₁.comp (Subgroup.topEquiv (G := V')).toMonoidHom, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro q
    obtain ⟨u, hu⟩ := hβs q
    exact ⟨⟨ρ u, trivial⟩, by
      show β₁ (ρ u) = q
      rw [hβ₁, hu]⟩
  · rintro ⟨y, hy⟩
    obtain ⟨u, rfl⟩ := hρs y
    show β₁ (ρ u) = 1 ↔ ρ u ∈ (⊥ : Subgroup V')
    rw [hβ₁, hβk, Subgroup.mem_bot, hρk]
  · rintro γ ⟨y, hy⟩ m hu hm hum
    obtain ⟨u, rfl⟩ := hρs y
    have hu₀ : ((π γ : ↥H) : MulAut V) (u : V) ∈ U := hUinv (π γ) u u.2
    have hum' : β u = QuotientGroup.mk m := by
      have : β₁ (ρ u) = QuotientGroup.mk m := hum
      rwa [hβ₁] at this
    have key := hβe γ u m hu₀ hm hum'
    have h2 := hτρ (π γ) u hu₀
    show β₁ (((τ (π γ) : ↥H') : MulAut V') (ρ u)) = _
    rw [h2, hβ₁]
    exact key

theorem realizesVia_injective_of_faithful {V : Type*} [CommGroup V] {D : FFModel}
    (hD : D.Faithful) {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : D.Gam →* ↥H}
    (h : D.RealizesVia H U Z π) : Function.Injective π := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  obtain ⟨_, _, _, hUinv, _, hsec, _, β, hβs, _, hβe⟩ := h
  apply hD
  intro m hm
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨m, hm⟩)
  have hact : D.act γ m ∈ D.sec := hsec γ m hm
  have hu' : ((π γ : ↥H) : MulAut V) (u : V) ∈ U := hUinv (π γ) u u.2
  have h1 := hβe γ u ⟨m, hm⟩ hu' hact hu
  have h2 : (⟨((π γ : ↥H) : MulAut V) (u : V), hu'⟩ : ↥U) = u := by
    apply Subtype.ext
    have h3 : ((π γ : ↥H) : MulAut V) = 1 := by rw [hγ]; rfl
    show ((π γ : ↥H) : MulAut V) (u : V) = (u : V)
    rw [h3]
    rfl
  rw [h2, hu] at h1
  have h3 := QuotientGroup.eq.mp h1
  have h4 : m⁻¹ * D.act γ m ∈ D.ker := h3
  rw [mul_comm]
  exact h4

theorem map_sup_inf_of_isSumMod {W Y : Type*} [Group W] [Group Y] (θ : W →* Y)
    {A B C Tot : Subgroup W} (hker : ∀ w, θ w = 1 ↔ w ∈ C) (h1 : Tot = A ⊔ B ⊔ C)
    (h2 : (A ⊔ C) ⊓ (B ⊔ C) ≤ C) :
    Tot.map θ = A.map θ ⊔ B.map θ ∧ A.map θ ⊓ B.map θ = ⊥ := by
  constructor
  · rw [h1, Subgroup.map_sup, Subgroup.map_sup]
    have hC : C.map θ = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨c, hc, rfl⟩
      rw [Subgroup.mem_bot]
      exact (hker c).mpr hc
    rw [hC, sup_bot_eq]
  · rw [eq_bot_iff]
    rintro y ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
    rw [Subgroup.mem_bot]
    have h3 : a⁻¹ * b ∈ C := by
      rw [← hker, map_mul, map_inv, hab, inv_mul_cancel]
    have h4 : b ∈ A ⊔ C := by
      have : a * (a⁻¹ * b) = b := by group
      rw [← this]
      exact (A ⊔ C).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right h3)
    have h5 : b ∈ C := h2 ⟨h4, Subgroup.mem_sup_left hb⟩
    rw [← hab]
    exact (hker b).mpr h5

theorem secIsoL_of_equivariant_iso {W : Type} {Y : Type*} [CommGroup W] [Group Y] (θ : W →* Y)
    {A : Subgroup (MulAut W)} {P Q : Subgroup W}
    (hP : A ≤ stabSub P) (hQ : A ≤ stabSub Q)
    (hker : ∀ w, θ w = 1 ↔ w ∈ fixV A) (φ : ↥(P.map θ) ≃* ↥(Q.map θ))
    (hφ : ∀ l ∈ A, ∃ g : Y, (∀ w : W, θ ((l : MulAut W) w) = g * θ w * g⁻¹) ∧
      ∀ x x' : ↥(P.map θ), (x' : Y) = g * (x : Y) * g⁻¹ → (φ x' : Y) = g * (φ x : Y) * g⁻¹) :
    SecIsoL A P (P ⊓ fixV A) Q (Q ⊓ fixV A) := by
  let ρ₁ : ↥P →* ↥(P.map θ) := θ.subgroupMap P
  let ρ₂ : ↥Q →* ↥(Q.map θ) := θ.subgroupMap Q
  have hρ₁s : Function.Surjective ρ₁ := θ.subgroupMap_surjective P
  have hρ₂s : Function.Surjective ρ₂ := θ.subgroupMap_surjective Q
  have hρ₁c : ∀ u : ↥P, ((ρ₁ u : ↥(P.map θ)) : Y) = θ (u : W) := fun u => rfl
  have hρ₂c : ∀ q : ↥Q, ((ρ₂ q : ↥(Q.map θ)) : Y) = θ (q : W) := fun q => rfl
  have hker2 : ρ₂.ker = (Q ⊓ fixV A).subgroupOf Q := by
    ext q
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hq
      have : θ (q : W) = 1 := by
        have := congrArg Subtype.val hq
        simpa [hρ₂c] using this
      exact ⟨q.2, (hker _).mp this⟩
    · rintro ⟨-, hq⟩
      exact Subtype.ext (by rw [hρ₂c]; exact (hker _).mpr hq)
  let ε : ↥(Q.map θ) ≃* ↥Q ⧸ (Q ⊓ fixV A).subgroupOf Q :=
    (QuotientGroup.quotientKerEquivOfSurjective ρ₂ hρ₂s).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker2)
  have hε : ∀ q : ↥Q, ε.symm (QuotientGroup.mk q) = ρ₂ q := fun q => rfl
  refine ⟨Function.surjective_id, inf_le_left, inf_le_left, fun h u hu => (hP h.2 u).mpr hu,
    fun h z hz => ⟨(hP h.2 z).mpr hz.1, ?_⟩, fun γ m hm => (hQ γ.2 m).mpr hm,
    fun γ m hm => ⟨(hQ γ.2 m).mpr hm.1, ?_⟩,
    (ε.toMonoidHom.comp (φ.toMonoidHom.comp ρ₁)), ?_, ?_, ?_⟩
  · have h1 : ((h : ↥A) : MulAut W) z = z := hz.2 h h.2
    rw [h1]
    exact hz.2
  · let γ' : ↥A := γ
    have h1 : (γ' : MulAut W) m = m := hm.2 γ' γ'.2
    show (γ' : MulAut W) m ∈ fixV A
    rw [h1]
    exact hm.2
  · exact ε.surjective.comp (φ.surjective.comp hρ₁s)
  · intro u
    show ε (φ (ρ₁ u)) = 1 ↔ _
    rw [map_eq_one_iff _ ε.injective, map_eq_one_iff _ φ.injective, Subgroup.mem_inf]
    constructor
    · intro hu
      have : θ (u : W) = 1 := by
        have := congrArg Subtype.val hu
        simpa [hρ₁c] using this
      exact ⟨u.2, (hker _).mp this⟩
    · rintro ⟨-, hu⟩
      exact Subtype.ext (by rw [hρ₁c]; exact (hker _).mpr hu)
  · intro γ u m hu hm hum
    let γ' : ↥A := γ
    let m' : ↥Q := m
    obtain ⟨g, hg1, hg2⟩ := hφ γ' γ'.2
    have hum' : φ (ρ₁ u) = ρ₂ m' := by
      have h1 : ε (φ (ρ₁ u)) = QuotientGroup.mk m' := hum
      rw [← hε m']
      exact (MulEquiv.eq_symm_apply ε).mpr h1
    show ε (φ (ρ₁ ⟨(γ' : MulAut W) (u : W), hu⟩)) =
      QuotientGroup.mk ⟨(γ' : MulAut W) (m' : W), hm⟩
    rw [← MulEquiv.eq_symm_apply, hε]
    apply Subtype.ext
    have h5 : ((ρ₁ ⟨(γ' : MulAut W) (u : W), hu⟩ : ↥(P.map θ)) : Y) =
        g * ((ρ₁ u : ↥(P.map θ)) : Y) * g⁻¹ := by
      rw [hρ₁c, hρ₁c]
      exact hg1 u
    have h6 := hg2 (ρ₁ u) _ h5
    rw [h6, hum', hρ₂c, hρ₂c]
    exact (hg1 (m' : W)).symm

end Transport

section Hat

attribute [local instance] CFSG.Quasithin.commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

@[expose] def ModelOnU {X : Type} [Group X] (D : FFModel) (Y A : Subgroup X) : Prop :=
  Y ≤ Subgroup.normalizer (A : Set X) ∧
    ∃ hA : IsElemAbelian 2 A, @FFModel.Realizes ↥A (commGroupOfElemAbelian hA) D (autOn Y A) ⊤ ⊥

theorem mem_hat_conjClosure_iff (h : HypF918 T V L V₁ Vp H K)
    {y : GhOf V₁ (conjClosure Vp H) (conjClosure K T)} :
    y ∈ hat' V₁ Vp H K T (conjClosure K T) ↔
      ∃ (k : G) (hk : k ∈ conjClosure K T), y = kbarOf h (h.K₀_le_H hk) := by
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := mem_secImg.mp hy
    obtain ⟨w, hw, hwz⟩ := mem_secImg.mp hz
    refine ⟨(w : G), hw, ?_⟩
    unfold kbarOf
    congr 1
    exact Subtype.ext hwz.symm
  · rintro ⟨k, hk, rfl⟩
    exact kbarOf_mem_hat h hk

theorem le_stabSub_fixV {W : Type*} [CommGroup W] (A : Subgroup (MulAut W)) :
    A ≤ stabSub (fixV A) := by
  intro g hg u
  have hfix : ∀ v ∈ fixV A, g v = v := fun v hv => hv g hg
  constructor
  · intro hgu
    have h1 : g⁻¹ (g u) = g u := hgu g⁻¹ (A.inv_mem hg)
    have h2 : g⁻¹ (g u) = u := by simp
    rw [h2] at h1
    exact h1.symm ▸ hgu
  · intro hu
    rw [hfix u hu]
    exact hu

variable [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]

noncomputable def tauHat (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hAV : autIH V₁ I H (conjClosure K T) ≤ stabSub (subM V₁ (conjClosure I H) I)) :
    ↥(autIH V₁ I H (conjClosure K T)) →* MulAut ↥(hat' V₁ Vp H K T I) :=
  (MulAut.congr (psiSec h hIU)).toMonoidHom.comp
    (B5.secHom (autIH V₁ I H (conjClosure K T)) hAV (le_stabSub_fixV _))

theorem tauHat_thetaV (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hAV : autIH V₁ I H (conjClosure K T) ≤ stabSub (subM V₁ (conjClosure I H) I))
    (x : ↥(autIH V₁ I H (conjClosure K T))) (u : ↥(subM V₁ (conjClosure I H) I))
    (hxu : ((x : MulAut ↥(tildeOf V₁ (conjClosure I H))) : ↥(tildeOf V₁ (conjClosure I H)) →
        ↥(tildeOf V₁ (conjClosure I H))) (u : ↥(tildeOf V₁ (conjClosure I H))) ∈
      subM V₁ (conjClosure I H) I) :
    tauHat h hIU hAV x (thetaV h hIU u) =
      thetaV h hIU ⟨(x : MulAut ↥(tildeOf V₁ (conjClosure I H))) (u : ↥(tildeOf V₁ (conjClosure I H))),
        hxu⟩ := by
  rw [← psiSec_mk]
  show (MulAut.congr (psiSec h hIU)) (B5.secHom _ hAV _ x) ((psiSec h hIU) (QuotientGroup.mk u)) = _
  rw [MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [B5.secHom_mk]
  rfl

theorem conjAct_hat_eq_tauHat (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hKI : conjClosure K T ≤ Subgroup.normalizer (I : Set G))
    (hAV : autIH V₁ I H (conjClosure K T) ≤ stabSub (subM V₁ (conjClosure I H) I))
    {y : G} (hy : y ∈ conjClosure K T)
    (hxA : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨y, h.K₀_le_H hy⟩ ∈
      autIH V₁ I H (conjClosure K T)) :
    conjAct (hat' V₁ Vp H K T I) ⟨kbarOf h (h.K₀_le_H hy),
        hatOf_le_normalizer hKI (kbarOf_mem_hat h hy)⟩ =
      tauHat h hIU hAV
        ⟨actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨y, h.K₀_le_H hy⟩, hxA⟩ := by
  refine MulEquiv.ext fun z => ?_
  obtain ⟨u, rfl⟩ := thetaV_surjective h hIU z
  have hxu := (hAV hxA (u : ↥(tildeOf V₁ (conjClosure I H)))).mpr u.2
  rw [tauHat_thetaV h hIU hAV _ u hxu]
  apply Subtype.ext
  rw [conjAct_apply_coe', thetaV_coe, thetaV_coe]
  exact (thetaMap_actH h hIU (h.K₀_le_H hy) u).symm

theorem modelOnU_of_realizes (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hKI : conjClosure K T ≤ Subgroup.normalizer (I : Set G))
    (hAV : autIH V₁ I H (conjClosure K T) ≤ stabSub (subM V₁ (conjClosure I H) I)) {D : FFModel}
    (hD : D.Realizes (autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I)
      (subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T)))) :
    ModelOnU D (hat' V₁ Vp H K T (conjClosure K T)) (hat' V₁ Vp H K T I) := by
  have hel : IsElemAbelian 2 (hat' V₁ Vp H K T I) :=
    isElemAbelian_secImg (h.isElemAbelian_tilde_of_le hIU)
  refine ⟨hatOf_le_normalizer hKI, hel, ?_⟩
  obtain ⟨π, hπ⟩ := hD
  letI : CommGroup ↥(hat' V₁ Vp H K T I) := commGroupOfElemAbelian hel
  have hτmem : ∀ x : ↥(autIH V₁ I H (conjClosure K T)), tauHat h hIU hAV x ∈
      autOn (hat' V₁ Vp H K T (conjClosure K T)) (hat' V₁ Vp H K T I) := by
    intro x
    have hx : (x : MulAut ↥(tildeOf V₁ (conjClosure I H))) ∈
        ((conjClosure K T).subgroupOf H).map
          (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)) := by
      rw [← autIH_eq_map h h.K₀_le_H]
      exact x.2
    obtain ⟨⟨y, hyH⟩, hy, hyx⟩ := hx
    have hyK : y ∈ conjClosure K T := Subgroup.mem_subgroupOf.mp hy
    have hxA : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨y, h.K₀_le_H hyK⟩ ∈
        autIH V₁ I H (conjClosure K T) := hyx ▸ x.2
    have hxe : x = ⟨actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
        ⟨y, h.K₀_le_H hyK⟩, hxA⟩ := Subtype.ext hyx.symm
    rw [hxe, ← conjAct_hat_eq_tauHat h hIU hKI hAV hyK hxA]
    exact mem_autOn_iff.mpr ⟨_, kbarOf_mem_hat h hyK, rfl⟩
  let τ : ↥(autIH V₁ I H (conjClosure K T)) →*
      ↥(autOn (hat' V₁ Vp H K T (conjClosure K T)) (hat' V₁ Vp H K T I)) :=
    (tauHat h hIU hAV).codRestrict _ hτmem
  have hτs : Function.Surjective τ := by
    rintro ⟨a, ha⟩
    obtain ⟨n, hnY, rfl⟩ := mem_autOn_iff.mp ha
    obtain ⟨k, hk, hnk⟩ := (mem_hat_conjClosure_iff h).mp hnY
    have hxA : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨k, h.K₀_le_H hk⟩ ∈
        autIH V₁ I H (conjClosure K T) := by
      rw [autIH_eq_map h h.K₀_le_H]
      exact ⟨⟨k, h.K₀_le_H hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    refine ⟨⟨_, hxA⟩, Subtype.ext ?_⟩
    have hne : n = ⟨kbarOf h (h.K₀_le_H hk),
        hatOf_le_normalizer hKI (kbarOf_mem_hat h hk)⟩ := Subtype.ext hnk
    have hconj : conjAct (hat' V₁ Vp H K T I) n = tauHat h hIU hAV ⟨_, hxA⟩ := by
      rw [hne]
      exact conjAct_hat_eq_tauHat h hIU hKI hAV hk hxA
    exact hconj.symm
  refine ⟨τ.comp π, realizesVia_transport (H' := autOn (hat' V₁ Vp H K T (conjClosure K T))
    (hat' V₁ Vp H K T I)) hπ (thetaV h hIU) (thetaV_surjective h hIU) ?_ τ hτs ?_⟩
  · intro u
    rw [← MonoidHom.mem_ker, ker_thetaV, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun hh => ⟨u.2, hh⟩, fun hh => hh.2⟩
  · intro x u hu
    exact tauHat_thetaV h hIU hAV x u hu

end Hat


end CFSG.Quasithin.RonanF918
