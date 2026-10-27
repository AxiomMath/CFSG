module

public import CFSG.Quasithin.Background.C58Transport
public import CFSG.Quasithin.Background.E2SolvStruct
public import CFSG.Quasithin.Background.C118BridgeAlg
public import CFSG.Quasithin.Background.C1PackA4
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245BaumannSetting
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce

public section

namespace CFSG.Quasithin.C58

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Campbell
  Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

section Transport

variable {H : Subgroup G}

theorem mem_centralizer_subgroupOf_iff' {X : Subgroup G} (hXH : X ≤ H) {g : H} :
    g ∈ centralizer (X.subgroupOf H : Set H) ↔ (g : G) ∈ centralizer (X : Set G) := by
  simp only [mem_centralizer_iff, SetLike.mem_coe, mem_subgroupOf]
  constructor
  · intro h x hx
    exact congrArg Subtype.val (h ⟨x, hXH hx⟩ hx)
  · intro h x hx
    exact Subtype.ext (h (x : G) hx)

theorem isTwoReducedIn_top_subgroupOf {V : Subgroup G} (h : IsTwoReducedIn H V) :
    IsTwoReducedIn (⊤ : Subgroup H) (V.subgroupOf H) := by
  obtain ⟨hVH, hHN, ⟨hcomm, hsq⟩, hD⟩ := h
  refine ⟨le_top, ?_, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · intro g _
    rw [mem_normalizer_iff]
    intro x
    simp only [mem_subgroupOf, coe_mul, coe_inv]
    exact mem_normalizer_iff.mp (hHN g.2) x
  · have := hcomm.is_comm.comm ⟨((a : H) : G), mem_subgroupOf.mp a.2⟩
      ⟨((b : H) : G), mem_subgroupOf.mp b.2⟩
    have h2 : ((a : H) : G) * ((b : H) : G) = ((b : H) : G) * ((a : H) : G) :=
      congrArg Subtype.val this
    exact Subtype.ext (Subtype.ext h2)
  · apply Subtype.ext
    simpa using hsq (x : G) (mem_subgroupOf.mp hx)
  · intro D _ hDn hDpow
    have hD₀H : D.map H.subtype ≤ H := Subgroup.map_subtype_le D
    have hD₀N : H ≤ normalizer ((D.map H.subtype : Subgroup G) : Set G) := by
      intro g hg
      rw [mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨d, hd, rfl⟩
        refine ⟨⟨g, hg⟩ * d * ⟨g, hg⟩⁻¹, ?_, rfl⟩
        exact (mem_normalizer_iff.mp (hDn (mem_top (⟨g, hg⟩ : H))) d).mp hd
      · rintro ⟨d, hd, hdx⟩
        have hxH : x ∈ H := by
          have : g⁻¹ * (g * x * g⁻¹) * g ∈ H := mul_mem (mul_mem (inv_mem hg) (hdx ▸ d.2)) hg
          simpa [mul_assoc] using this
        refine ⟨⟨x, hxH⟩, ?_, rfl⟩
        have h1 := (mem_normalizer_iff.mp (hDn (mem_top (⟨g, hg⟩ : H))) ⟨x, hxH⟩).mpr
        apply h1
        have : (⟨g, hg⟩ : H) * ⟨x, hxH⟩ * (⟨g, hg⟩ : H)⁻¹ = d := Subtype.ext hdx.symm
        rw [this]; exact hd
    have hD₀ := hD (D.map H.subtype) hD₀H hD₀N (by
      rintro _ ⟨d, hd, rfl⟩
      obtain ⟨k, hk⟩ := hDpow d hd
      refine ⟨k, ?_⟩
      rw [mem_centralizer_subgroupOf_iff' hVH] at hk
      simpa using hk)
    intro d hd
    rw [mem_centralizer_subgroupOf_iff' hVH]
    exact hD₀ ⟨d, hd, rfl⟩

theorem map_oddOrderSubgroup_top (H : Subgroup G) :
    (oddOrderSubgroup (⊤ : Subgroup H)).map H.subtype = oddOrderSubgroup H := by
  unfold oddOrderSubgroup
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨-, hx⟩, rfl⟩
    exact ⟨x.2, by rw [subtype_apply, Subgroup.orderOf_coe]; exact hx⟩
  · rintro ⟨hyH, hy⟩
    exact ⟨⟨y, hyH⟩, ⟨mem_top _, by rw [Subgroup.orderOf_mk]; exact hy⟩, rfl⟩

theorem oddOrderSubgroup_eq_oTwoUpper (H : Subgroup G) : oddOrderSubgroup H = oTwoUpper H := rfl

theorem oddOrderSubgroup_top_eq [Finite G] (H : Subgroup G) :
    oddOrderSubgroup (⊤ : Subgroup H) = (oTwoUpper H).subgroupOf H := by
  have h := map_oddOrderSubgroup_top H
  rw [oddOrderSubgroup_eq_oTwoUpper H] at h
  rw [← h]
  exact (Subgroup.comap_map_eq_self_of_injective H.subtype_injective _).symm

theorem characteristic_map_mulEquiv {A B : Type*} [Group A] [Group B] {K : Subgroup A}
    (hK : K.Characteristic) (e : A ≃* B) : (K.map e.toMonoidHom).Characteristic := by
  refine Subgroup.characteristic_iff_map_eq.mpr fun φ => ?_
  have h := Subgroup.characteristic_iff_map_eq.mp hK ((e.trans φ).trans e.symm)
  rw [Subgroup.map_map]
  calc K.map (φ.toMonoidHom.comp e.toMonoidHom)
      = (K.map ((e.trans φ).trans e.symm).toMonoidHom).map e.toMonoidHom := by
        rw [Subgroup.map_map]; congr 1; ext x; simp
    _ = K.map e.toMonoidHom := by rw [h]

theorem noCharNormal_top_subgroupOf {S : Subgroup G} (hSH : S ≤ H)
    (hnc : ∀ C : Subgroup G, C ≤ S → C ≠ ⊥ → (C.subgroupOf S).Characteristic →
      ¬ H ≤ normalizer (C : Set G)) :
    NoCharNormal (S.subgroupOf H) (⊤ : Subgroup H) := by
  intro C hCS hC1 hCchar hCn
  have hCS' : C.map H.subtype ≤ S := by
    rintro _ ⟨c, hc, rfl⟩; exact mem_subgroupOf.mp (hCS hc)
  refine hnc (C.map H.subtype) hCS' ?_ ?_ ?_
  · intro h
    exact hC1 ((Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp h)
  · set e : ↥(S.subgroupOf H) ≃* ↥S := Subgroup.subgroupOfEquivOfLe hSH
    have he : (C.subgroupOf (S.subgroupOf H)).map e.toMonoidHom =
        (C.map H.subtype).subgroupOf S := by
      ext x
      simp only [mem_map, mem_subgroupOf]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨(y : H), hy, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        have hyS : (y : G) ∈ S := by rw [show (y : G) = x from hyx]; exact x.2
        refine ⟨⟨y, mem_subgroupOf.mpr hyS⟩, hy, ?_⟩
        exact Subtype.ext hyx
    rw [← he]
    exact characteristic_map_mulEquiv hCchar e
  · intro g hg
    have h1 := hCn (mem_top (⟨g, hg⟩ : H))
    rw [mem_normalizer_iff] at h1 ⊢
    intro x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨g, hg⟩ * c * ⟨g, hg⟩⁻¹, (h1 c).mp hc, rfl⟩
    · rintro ⟨c, hc, hcx⟩
      have hxH : x ∈ H := by
        have : g⁻¹ * (g * x * g⁻¹) * g ∈ H := mul_mem (mul_mem (inv_mem hg) (hcx ▸ c.2)) hg
        simpa [mul_assoc] using this
      refine ⟨⟨x, hxH⟩, (h1 ⟨x, hxH⟩).mpr ?_, rfl⟩
      have : (⟨g, hg⟩ : H) * ⟨x, hxH⟩ * (⟨g, hg⟩ : H)⁻¹ = c := Subtype.ext hcx.symm
      rw [this]; exact hc

theorem charTwo_top_of_charTwo (h : CharTwo H) : CharTwo (⊤ : Subgroup H) := by
  have := Ch1.charTwo_subgroupOf (le_refl H) h
  rwa [Subgroup.subgroupOf_self] at this

end Transport

section CommV

variable {V : Type*} [CommGroup V]

theorem commV_invariant' {X : Subgroup (MulAut V)} {x : MulAut V} (hx : x ∈ X) {w : V}
    (hw : w ∈ commV X) : x w ∈ commV X :=
  CFSG.Quasithin.commV_apply_mem_of_mem hx hw

theorem exists_proj {A B : Subgroup V} (hinf : A ⊓ B = ⊥) (hsup : A ⊔ B = ⊤) :
    ∃ π : V →* B, (∀ b : B, π b = b) ∧ ∀ v : V, π v = 1 ↔ v ∈ A := by
  classical
  let ι : ↥A × ↥B →* V := A.subtype.coprod B.subtype
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    have hab' : (a : V) * b = 1 := hab
    have hb : (b : V) = (a : V)⁻¹ := eq_inv_of_mul_eq_one_right hab'
    have hbA : (b : V) ∈ A ⊓ B := Subgroup.mem_inf.mpr ⟨by rw [hb]; exact inv_mem a.2, b.2⟩
    rw [hinf] at hbA
    have hb1 : b = 1 := Subtype.ext (mem_bot.mp hbA)
    have ha1 : a = 1 := Subtype.ext (by rw [hb1] at hab'; simpa using hab')
    rw [ha1, hb1]; rfl
  have hιsurj : Function.Surjective ι := by
    intro x
    have hx : x ∈ A ⊔ B := hsup ▸ mem_top x
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup.mp hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  let e : ↥A × ↥B ≃* V := MulEquiv.ofBijective ι ⟨hιinj, hιsurj⟩
  refine ⟨(MonoidHom.snd ↥A ↥B).comp e.symm.toMonoidHom, fun b => ?_, fun v => ?_⟩
  · have h1 : e (1, b) = b := by
      show (1 : V) * b = b
      rw [one_mul]
    have h2 : e.symm b = (1, b) := by rw [MulEquiv.symm_apply_eq]; exact h1.symm
    show (e.symm b).2 = b
    rw [h2]
  · constructor
    · intro hv
      have hv' : (e.symm v).2 = 1 := hv
      have h1 : e (e.symm v) = v := e.apply_symm_apply v
      have h2 : e (e.symm v) = ((e.symm v).1 : V) * ((e.symm v).2 : V) := rfl
      rw [h2, hv', Subgroup.coe_one, mul_one] at h1
      rw [← h1]; exact (e.symm v).1.2
    · intro hv
      have h1 : e (⟨v, hv⟩, 1) = v := by
        show v * (1 : V) = v
        rw [mul_one]
      have h2 : e.symm v = (⟨v, hv⟩, 1) := by rw [MulEquiv.symm_apply_eq]; exact h1.symm
      show (e.symm v).2 = 1
      rw [h2]

end CommV

section Push

variable [Finite G]

theorem pushUp_block {H₀ S M : Subgroup G} (hmin : MinParabolic H₀ S M)
    (hsolv : Group.IsSolvable H₀)
    (hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p H₀ ≤ 2)
    (hchar : CharTwo H₀) (hbaum : baum S = S)
    (hnc : ∀ C : Subgroup G, C ≤ S → C ≠ ⊥ → (C.subgroupOf S).Characteristic →
      ¬ H₀ ≤ normalizer (C : Set G)) :
    IsShort2 (oTwoUpper H₀) ∧ IsAltType (oTwoUpper H₀) 3 ∧
      ⁅oTwoUpper H₀, thompsonJ S⁆ = oTwoUpper H₀ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := hmin.isSylow
  have hSH : S ≤ H₀ := hS.1
  have hS2 : IsPGroup 2 S := hS.2.1
  have hS1 : S ≠ ⊥ := by
    intro h
    apply hmin.not_normal
    rw [h]
    intro g _
    rw [mem_normalizer_iff]
    intro x
    simp only [mem_bot]
    constructor
    · rintro rfl; group
    · intro hx
      have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [this, hx]; group
  set Z := quasithinOmegaOneCenter S with hZ
  set V := conjClosure Z H₀ with hV
  have hred : IsTwoReducedIn H₀ V :=
    isTwoReducedIn_conjClosure_of_sylowIn hSH hS2 hS.2.2 hchar le_rfl
  have hVe : IsElemAbelian 2 V := hred.2.2.1
  have hHN : H₀ ≤ normalizer (V : Set G) := hred.2.1
  have hZ1 : Z ≠ ⊥ := quasithinOmegaOneCenter_ne_bot hS2 hS1
  have hZS : Z ≤ S := by
    rw [hZ, ← omegaOneCenterOf_eq]
    exact C1GN.omegaOneCenterOf_le_self S
  have hZchar : (Z.subgroupOf S).Characteristic := characteristic_omegaOneCenterOf S
  have hHV : ¬ H₀ ≤ centralizer (V : Set G) := by
    intro h
    refine hnc Z hZS hZ1 hZchar fun g hg => ?_
    have hgc : g ∈ centralizer (Z : Set G) :=
      Subgroup.centralizer_le (le_conjClosure Z H₀) (h hg)
    exact Subgroup.centralizer_le_normalizer _ hgc
  have hJ : ¬ thompsonJ S ≤ centralizer (V : Set G) := by
    intro h
    have hinf := hmin.inf_centralizer_eq_pCoreOf hred hHV
    have hJQ : thompsonJ S ≤ pCoreOf 2 H₀ := hinf ▸ le_inf (B6.thompsonJ_le S) h
    have hQS : pCoreOf 2 H₀ ≤ S := B6.pCoreOf_two_le_of_isSylowTwoOf hS
    have hJeq : thompsonJ (pCoreOf 2 H₀) = thompsonJ S := B6.thompsonJ_eq_of_le hJQ hQS
    refine hnc (thompsonJ S) (B6.thompsonJ_le S) (thompsonJ_ne_bot hS2 hS1)
      (characteristic_thompsonJ S) ?_
    rw [← hJeq]
    exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H₀).trans
      (normalizer_le_normalizer_thompsonJ _)
  obtain ⟨-, I, hIcard, hJHeq, hcomm, -, htrans, hnat, hsup, hinf, -⟩ :=
    E2_3_one_of_isSolvable hVe hmin hsolv hSQT hred hJ
  obtain ⟨hbaumJ, -⟩ := E2_3_two_sylow_of_isSolvable hVe hmin hsolv hSQT hred hJ
  have hIne : I.Nonempty := by
    rw [← Finset.card_pos]; rcases hIcard with h | h <;> omega
  obtain ⟨L, hL⟩ := hIne
  have hNL : autI hVe (thompsonJ H₀) ≤ normalizer (L : Set (MulAut (IntMod V hVe))) := by
    rw [hJHeq]
    refine iSup₂_le fun L' hL' => ?_
    by_cases hLL : L' = L
    · rw [hLL]; exact Subgroup.le_normalizer
    · refine le_trans ?_ (Subgroup.centralizer_le_normalizer (L : Set (MulAut (IntMod V hVe))))
      intro a ha
      rw [mem_centralizer_iff]
      intro b hb
      exact (hcomm L' hL' L hL hLL a ha b hb).symm
  have hI1 : ∀ L' ∈ I, L' = L := by
    intro L' hL'
    obtain ⟨t, ht, hte⟩ := htrans L hL L' hL'
    have htJ : t ∈ autI hVe (thompsonJ H₀) := by
      have h1 : t ∈ autI hVe (thompsonJ S) := by rw [← hbaumJ, hbaum]; exact ht
      exact autI_mono hVe (thompsonJ_le_thompsonJ_of_isSylowTwoOf hS) h1
    have htN := hNL htJ
    rw [← hte]
    ext y
    rw [B1.mem_conjAut]
    constructor
    · intro hy
      have := (mem_normalizer_iff.mp htN (t⁻¹ * y * t)).mp hy
      simpa [mul_assoc] using this
    · intro hy
      have := (mem_normalizer_iff.mp (inv_mem htN) y).mp hy
      simpa [mul_assoc] using this
  set A := fixV (autI hVe (twoResidual H₀)) with hA
  have hsup' : A ⊔ commV L = ⊤ := by
    rw [← E2.iSup_eq_of_singleton (f := commV) hL hI1]; exact hsup
  have hinf' : A ⊓ commV L = ⊥ := by
    rw [← E2.iSup_eq_of_singleton (f := commV) hL hI1]; exact hinf
  obtain ⟨eL, φ₀, hφ₀⟩ := hnat L hL
  obtain ⟨π, hπB, hπA⟩ := exists_proj hinf' hsup'
  set β : IntMod V hVe →* Multiplicative (Fin 2 → ZMod 2) := φ₀.toMonoidHom.comp π with hβ
  have hβB : ∀ b : ↥(commV L), β b = φ₀ b := fun b => by
    show φ₀ (π b) = φ₀ b
    rw [hπB]
  have hβs : Function.Surjective β := by
    intro y
    refine ⟨(φ₀.symm y : IntMod V hVe), ?_⟩
    rw [hβB, MulEquiv.apply_symm_apply]
  have hβ1 : ∀ u, β u = 1 ↔ u ∈ A := by
    intro u
    rw [← hπA]
    show φ₀ (π u) = 1 ↔ π u = 1
    exact ⟨fun h => φ₀.injective (h.trans (map_one φ₀).symm), fun h => by rw [h, map_one]⟩
  set act := convHom hVe H₀ hHN with hact
  have hactv : ∀ (g : H₀) (u : IntMod V hVe), (act g u).val = (g : G) * u.val * (g : G)⁻¹ := by
    intro g u
    rw [hact, convHom_apply, convI_apply_val]
  have hKN : twoResidual H₀ ≤ normalizer (V : Set G) := (twoResidual_le H₀).trans hHN
  have hAinv : ∀ (g : H₀) (a : IntMod V hVe), a ∈ A → act g a ∈ A := by
    intro g a ha
    rw [hA, mem_fixV_autI hVe hKN] at ha ⊢
    rw [hactv]
    have hgN : (g : G) ∈ normalizer (centralizer (twoResidual H₀ : Set G) : Set G) :=
      B6.le_normalizer_centralizer (le_normalizer_twoResidual H₀) g.2
    exact (mem_normalizer_iff.mp hgN _).mp ha
  have hker : ∀ g u v, β u = β v → β (act g u) = β (act g v) := by
    intro g u v huv
    have h1 : u * v⁻¹ ∈ A := by
      rw [← hβ1, map_mul, map_inv, huv]
      exact mul_inv_cancel (β v)
    have h2 := hAinv g _ h1
    rw [map_mul, map_inv] at h2
    rw [← hβ1, map_mul, map_inv] at h2
    exact mul_inv_eq_one.mp h2
  obtain ⟨ρ₀, hρ₀⟩ := exists_sl2_action act β hβs (ZMod.card 2) hker
  have hLH : L ≤ autI hVe H₀ := by
    have h1 : L ≤ autI hVe (thompsonJ H₀) := by
      rw [hJHeq]; exact le_iSup₂_of_le L hL le_rfl
    exact h1.trans (autI_mono hVe (thompsonJ_le_self H₀))
  have hρsurj : ∀ A' : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), ∃ g : H₀, ρ₀ g = A' := by
    intro A'
    set l : L := eL.symm A' with hl
    obtain ⟨g, hgH, hgl⟩ := (mem_autI hVe).1 (hLH l.2)
    refine ⟨⟨g, hgH⟩, ?_⟩
    have hactl : ∀ u, act ⟨g, hgH⟩ u = (l : MulAut (IntMod V hVe)) u := by
      intro u
      rw [hact, convHom_apply]
      exact congrArg (fun φ : MulAut (IntMod V hVe) => φ u) hgl
    apply Subtype.ext
    apply B1.mulVec_ext
    intro x
    obtain ⟨w, hw⟩ := φ₀.surjective (Multiplicative.ofAdd x)
    have hlw : (l : MulAut (IntMod V hVe)) (w : IntMod V hVe) ∈ commV L :=
      commV_invariant' l.2 w.2
    have e1 := hρ₀ ⟨g, hgH⟩ (w : IntMod V hVe)
    have e2 := hφ₀ l w hlw
    rw [hactl, show (l : MulAut (IntMod V hVe)) (w : IntMod V hVe) =
      ((⟨_, hlw⟩ : ↥(commV L)) : IntMod V hVe) from rfl, hβB, hβB, e2, hw, hl,
      MulEquiv.apply_symm_apply] at e1
    simpa using e1.symm
  set R' : Subgroup H₀ := S.subgroupOf H₀ with hR'
  set M' : Subgroup H₀ := M.subgroupOf H₀ with hM'
  set V' : Subgroup H₀ := V.subgroupOf H₀ with hV'
  have hmin' := hmin.subgroupOf
  have hVH : V ≤ H₀ := hred.1
  let toV : V' →* IntMod V hVe :=
    { toFun := fun v => IntMod.mk hVe ⟨((v : H₀) : G), mem_subgroupOf.mp v.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have htoV : ∀ v : V', (toV v).val = ((v : H₀) : G) := fun _ => rfl
  let φ : V' →* Multiplicative (Fin 2 → ZMod 2) := β.comp toV
  let ρ : H₀ →* Gamma (ZMod 2) :=
    ((slPerm (ZMod 2)).comp ρ₀).codRestrict (Gamma (ZMod 2)) fun g => slPerm_mem_Gamma (ρ₀ g)
  have hρ : ∀ g : H₀, ((ρ g : Gamma (ZMod 2)) : Equiv.Perm (Fin 2 → ZMod 2)) =
      slPerm (ZMod 2) (ρ₀ g) := fun _ => rfl
  have hodd : oddOrderSubgroup (⊤ : Subgroup H₀) = (twoResidual H₀).subgroupOf H₀ := by
    rw [oddOrderSubgroup_top_eq, F6.twoResidual_eq_oTwoUpper]
  have hset : IsNatQuotSetting R' M' V' ρ φ :=
    { sylow := hmin'.isSylow
      nonnormal := fun hn => hmin'.not_normal (by
        rw [Subgroup.normalizer_eq_top_iff.mpr hn])
      le_M := hmin'.le
      M_lt := hmin'.maximal.1
      M_max := fun Y hRY hY => hmin'.le_of_lt hRY hY
      reduced := isTwoReducedIn_top_subgroupOf hred
      sl_le := fun A' => by
        obtain ⟨g, hg⟩ := hρsurj A'
        exact ⟨g, by rw [hρ, hg]⟩
      two_quot := fun g => ⟨0, by
        rw [pow_zero, pow_one]
        exact mem_slGamma_iff.mpr ⟨ρ₀ g, rfl⟩⟩
      φ_surj := by
        intro y
        obtain ⟨u, hu⟩ := hβs y
        refine ⟨⟨⟨u.val, hVH u.val_mem⟩, mem_subgroupOf.mpr u.val_mem⟩, ?_⟩
        show β (toV _) = y
        rw [← hu]
        rfl
      φ_equiv := by
        intro g v v' hv'
        have h1 : toV v' = act g (toV v) := by
          apply IntMod.val_injective
          rw [hactv, htoV, htoV, hv']
          rfl
        show Multiplicative.toAdd (β (toV v')) = _
        rw [h1, hρ₀ g (toV v), hρ, slPerm_apply, Matrix.SpecialLinearGroup.smul_def]
        rfl
      φ_ker := by
        ext v
        rw [MonoidHom.mem_ker, mem_subgroupOf, hodd,
          mem_centralizer_subgroupOf_iff' (twoResidual_le H₀)]
        show β (toV v) = 1 ↔ _
        rw [hβ1, hA, mem_fixV_autI hVe hKN, htoV] }
  have hchar' : CharTwo (⊤ : Subgroup H₀) := charTwo_top_of_charTwo hchar
  have hnc' : NoCharNormal R' ⊤ := noCharNormal_top_subgroupOf hSH hnc
  have hJmap := C56.elemThompsonIn_subgroupOf_map hSH
  have hJ' : ⁅elemThompsonIn 2 R', V'⁆ ≠ ⊥ := by
    intro hbot
    apply hJ
    intro j hj
    rw [← hJmap] at hj
    obtain ⟨j', hj', rfl⟩ := hj
    rw [mem_centralizer_iff]
    intro v hv
    have hmem : ⁅j', (⟨v, hVH hv⟩ : H₀)⁆ ∈ ⁅elemThompsonIn 2 R', V'⁆ :=
      Subgroup.commutator_mem_commutator hj' (mem_subgroupOf.mpr hv)
    rw [hbot, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact (congrArg Subtype.val hmem).symm
  have hcard2 : Nat.card (ZMod 2) = 2 ^ 1 := by rw [Nat.card_eq_fintype_card, ZMod.card]; rfl
  obtain ⟨-, hchi, hthJ, -, hn1⟩ :=
    hset.actual_Campbell_natural_minimal_parabolic_chi0_block hchar' hnc' hJ' le_rfl hcard2
  obtain ⟨halt', -⟩ := hn1 rfl
  set L₀' := oddOrderSubgroup (⊤ : Subgroup H₀) with hL₀'
  have hmap : L₀'.map H₀.subtype = oTwoUpper H₀ := map_oddOrderSubgroup_top H₀
  have h3' : Nat.card (↥L₀' ⧸ CFSG.pCore 2 ↥L₀') = 3 := by
    obtain ⟨α, hαs, hαk, -⟩ := halt'
    have e := QuotientGroup.quotientKerEquivOfSurjective α hαs
    rw [← hαk, Nat.card_congr e.toEquiv]
    have h6 := two_mul_nat_card_alternatingGroup (α := Fin 3)
    rw [Nat.card_perm, Nat.card_fin] at h6
    simp only [Nat.factorial] at h6
    omega
  have hshort : IsShort2 (oTwoUpper H₀) := by
    rw [← hmap]
    exact isShort2_map_of_injective H₀.subtype_injective hchi.1.1 h3'
  have h3 : Nat.card (↥(oTwoUpper H₀) ⧸ CFSG.pCore 2 ↥(oTwoUpper H₀)) = 3 := by
    rw [← hmap, card_quotient_pCore_map H₀.subtype_injective]
    exact h3'
  refine ⟨hshort, C1Pack.isAltType_three_of_card_three hshort h3, ?_⟩
  have h := congrArg (Subgroup.map H₀.subtype) hthJ
  rw [Subgroup.map_commutator, hmap, hJmap] at h
  exact h

end Push

end CFSG.Quasithin.C58
