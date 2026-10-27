module

public import CFSG.Walter.W67.Lemma22

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise
open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace Frame

variable {h : Hyp G} (fr : Frame h)

theorem conj_mem_E {n x : G} (hn : n ∈ Subgroup.normalizer ((fr.S : Subgroup G) : Set G))
    (hx : x ∈ fr.E) : n * x * n⁻¹ ∈ fr.E := by
  refine fr.mem_E_of_odd (Subgroup.mem_centralizer_iff.mpr fun s hs => ?_) ?_
  · have hs' : n⁻¹ * s * n⁻¹⁻¹ ∈ (fr.S : Subgroup G) :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) s).mp hs
    have hc := Subgroup.mem_centralizer_iff.mp (fr.E_le_CS hx) _ hs'
    calc s * (n * x * n⁻¹) = n * ((n⁻¹ * s * n⁻¹⁻¹) * x) * n⁻¹ := by group
      _ = n * (x * (n⁻¹ * s * n⁻¹⁻¹)) * n⁻¹ := by rw [hc]
      _ = n * x * n⁻¹ * s := by group
  · rw [orderOf_conj_mul]
    exact odd_orderOf_of_mem_oddPart hx

theorem normalizer_S_eq
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) :
    Subgroup.normalizer ((fr.S : Subgroup G) : Set G) =
      (Subgroup.normalizer ((fr.S : Subgroup G) : Set G) ⊓
        Subgroup.centralizer (fr.E : Set G)) ⊔ fr.CS := by
  set NS := Subgroup.normalizer ((fr.S : Subgroup G) : Set G) with hNS
  set M := NS ⊓ Subgroup.centralizer (fr.E : Set G) with hM
  obtain ⟨e', P₀, hT⟩ := fr.exists_coords
  obtain ⟨y, hy3, hyN, hyfix⟩ :=
    PSL2Sub.exists_fixed_three e' h.odd_p hT h.mod_eight
  set u := psl2Emb e' y with hu
  have huK : u ∈ h.K := PSL2Sub.emb_mem e' y
  have hu3 : orderOf u = 3 := by
    rw [hu, orderOf_injective _ (PSL2Sub.emb_injective e'), hy3]
  have huH : u ∈ h.H := h.K_le_H huK
  have huNH : u ∈ NS ⊓ h.H := by
    rw [fr.normalizer_S_inf_H]
    exact ⟨huH, hyN⟩
  have huE : u ∈ Subgroup.centralizer (fr.E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨σ, hσ⟩ := fr.conj_eq_fieldAut hT hx
    have := hσ y
    rw [hyfix σ] at this
    calc x * u = (x * u * x⁻¹) * x := by group
      _ = u * x := by rw [show x * u * x⁻¹ = u from this]
  have huC : u ∉ Subgroup.centralizer (fr.T : Set G) := by
    intro huC
    have : u ∈ h.K ⊓ Subgroup.centralizer (fr.T : Set G) := ⟨huK, huC⟩
    rw [PSL2Sub.inf_centralizer_eq h.iso h.odd_p h.f_pos fr.T_le_K fr.isKleinFour_T] at this
    have h4 : orderOf u ∣ 4 := fr.card_T ▸ Subgroup.orderOf_dvd_natCard _ this
    rw [hu3] at h4
    omega
  have huCS : u ∉ fr.CS := fun h' => huC (fr.CS_le_centralizer_T h')
  have hufree : ∀ t ∈ fr.T, u * t * u⁻¹ = t → t = 1 := fun t ht hut =>
    JT.eq_one_of_conj_eq_of_orderOf_eq_three fr.isKleinFour_T hu3 hyN huC ht hut
  have hCSNH : fr.CS ≤ NS ⊓ h.H := by
    rw [fr.normalizer_S_inf_H]
    exact fr.CS_le_normalizer_T
  have hidx3 : (fr.CS.relIndex (NS ⊓ h.H)).Prime := by
    rw [Subgroup.relIndex, fr.normalizer_S_inf_H, fr.index_CS_and_normalizer_T.1]
    exact Nat.prime_three
  have hNH : NS ⊓ h.H = Subgroup.zpowers u ⊔ fr.CS := by
    rcases eq_or_eq_of_relIndex_prime (le_sup_right : fr.CS ≤ Subgroup.zpowers u ⊔ fr.CS)
      (sup_le ((Subgroup.zpowers_le).mpr huNH) hCSNH) hidx3 with h1 | h1
    · exact absurd (h1 ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers u)) huCS
    · exact h1.symm
  have hCSNS : fr.CS ≤ NS := Subgroup.centralizer_le_normalizer _
  have hle1 : NS ⊓ h.H ≤ M ⊔ fr.CS := by
    rw [hNH]
    exact sup_le_sup_right ((Subgroup.zpowers_le).mpr (Subgroup.mem_inf.mpr ⟨huNH.1, huE⟩)) _
  have hle2 : M ⊔ fr.CS ≤ NS := sup_le inf_le_left hCSNS
  have hidx7 : ((NS ⊓ h.H).relIndex NS).Prime := by
    rw [fr.relIndex_normalizer_S_inf_H hidx]
    norm_num
  rcases eq_or_eq_of_relIndex_prime hle1 hle2 hidx7 with h1 | h1
  · exfalso
    obtain ⟨t, htT, ht1⟩ : ∃ t ∈ fr.T, t ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : fr.T = ⊥ := eq_bot_iff.mpr fun x hx => hcon x hx
      have h4 : Nat.card fr.T = 4 := fr.card_T
      rw [this, Subgroup.card_bot] at h4
      omega
    obtain ⟨n, hn, hnt⟩ := fr.exists_conj_of_mem_S hidx (fr.T_le_S htT) ht1 fr.J_mem
      h.J_ne_one
    have hnuM : n * u * n⁻¹ ∈ M := by
      refine Subgroup.mem_inf.mpr ⟨NS.mul_mem (NS.mul_mem hn huNH.1) (NS.inv_mem hn),
        Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      have hx' : n⁻¹ * x * n⁻¹⁻¹ ∈ fr.E := fr.conj_mem_E (NS.inv_mem hn) hx
      have hc := Subgroup.mem_centralizer_iff.mp huE _ hx'
      calc x * (n * u * n⁻¹) = n * ((n⁻¹ * x * n⁻¹⁻¹) * u) * n⁻¹ := by group
        _ = n * (u * (n⁻¹ * x * n⁻¹⁻¹)) * n⁻¹ := by rw [hc]
        _ = n * u * n⁻¹ * x := by group
    have hnuH : n * u * n⁻¹ ∈ h.H := (h1 ▸ Subgroup.mem_sup_left hnuM : _ ∈ NS ⊓ h.H).2
    have hc := h.commute_J hnuH
    apply ht1
    apply hufree t htT
    rw [← hnt] at hc
    have : u * t = t * u := by
      calc u * t = n⁻¹ * (n * u * n⁻¹ * (n * t * n⁻¹)) * n := by group
        _ = n⁻¹ * (n * t * n⁻¹ * (n * u * n⁻¹)) * n := by rw [hc]
        _ = t * u := by group
    rw [this, mul_inv_cancel_right]
  · exact h1.symm

theorem normalizer_inf_H_eq
    {X : Subgroup G} (hXE : X ≤ fr.E) :
    Subgroup.normalizer (X : Set G) ⊓ h.H =
      Subgroup.zpowers h.J ⊔ (h.KX X ⊔ fr.EX X) := by
  have hEN : fr.E ≤ Subgroup.normalizer (h.K : Set G) := fr.E_le_normalizer_K
  have hJX : h.J ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (fr.E_le_CS (hXE hx)) _ fr.J_mem).symm
  have hJN : h.J ∈ Subgroup.normalizer (X : Set G) := Subgroup.centralizer_le_normalizer _ hJX
  apply le_antisymm
  · rintro x ⟨hxN, hxH⟩
    rw [fr.isInternalDirectProduct_H.1.symm] at hxH
    have hKEN : h.K ⊔ fr.E ≤ Subgroup.normalizer
        ((Subgroup.zpowers h.J : Subgroup G) : Set G) := by
      intro y hy
      have hyH : y ∈ h.H := sup_le h.K_le_H fr.E_le_H hy
      rw [JT.normalizer_zpowers_of_orderOf_eq_two h.orderOf_J]
      exact hyH
    obtain ⟨j, hj, z, hz, rfl⟩ := (mem_sup_iff_of_le_normalizer hKEN).mp hxH
    obtain ⟨k, hk, e, he, rfl⟩ := (mem_sup_iff_of_le_normalizer hEN).mp hz
    have hjN : j ∈ Subgroup.normalizer (X : Set G) :=
      (Subgroup.zpowers_le (H := Subgroup.normalizer (X : Set G))).mpr hJN hj
    have hkeN : k * e ∈ Subgroup.normalizer (X : Set G) := by
      have : k * e = j⁻¹ * (j * (k * e)) := by group
      rw [this]
      exact mul_mem (Subgroup.inv_mem _ hjN) hxN
    have hcomm : ∀ x ∈ X, k * (e * x * e⁻¹) = (e * x * e⁻¹) * k := by
      intro x hx
      set x' := e * x * e⁻¹
      have hx'E : x' ∈ fr.E := (Subgroup.mul_mem _ (Subgroup.mul_mem _ he (hXE hx))
        (Subgroup.inv_mem _ he))
      have h1 : k * x' * k⁻¹ ∈ X := by
        have := (Subgroup.mem_normalizer_iff.mp hkeN x).mp hx
        have heq : k * e * x * (k * e)⁻¹ = k * x' * k⁻¹ := by simp only [x']; group
        rwa [heq] at this
      have hcE : k * x' * k⁻¹ * x'⁻¹ ∈ fr.E :=
        Subgroup.mul_mem _ (hXE h1) (Subgroup.inv_mem _ hx'E)
      have hcK : k * x' * k⁻¹ * x'⁻¹ ∈ h.K := by
        have : k * x' * k⁻¹ * x'⁻¹ = k * (x' * k⁻¹ * x'⁻¹) := by group
        rw [this]
        exact mul_mem hk (h.conj_mem_K (fr.E_le_H hx'E) (h.K.inv_mem hk))
      have h1' : k * x' * k⁻¹ * x'⁻¹ ∈ h.K ⊓ fr.E := ⟨hcK, hcE⟩
      rw [fr.K_inf_E, Subgroup.mem_bot] at h1'
      calc k * x' = (k * x' * k⁻¹ * x'⁻¹) * x' * k := by group
        _ = x' * k := by rw [h1', one_mul]
    have heN : e ∈ Subgroup.normalizer (X : Set G) := by
      refine JT.mem_normalizer_of_conj_mem fun x hx => ?_
      have := (Subgroup.mem_normalizer_iff.mp hkeN x).mp hx
      have heq : k * e * x * (k * e)⁻¹ = e * x * e⁻¹ := by
        calc k * e * x * (k * e)⁻¹ = (k * (e * x * e⁻¹)) * k⁻¹ := by group
          _ = (e * x * e⁻¹) * k * k⁻¹ := by rw [hcomm x hx]
          _ = e * x * e⁻¹ := by group
      rwa [heq] at this
    have hkC : k ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx₀ : e⁻¹ * x * e⁻¹⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ heN) x).mp hx
      have := hcomm _ hx₀
      have heq : e * (e⁻¹ * x * e⁻¹⁻¹) * e⁻¹ = x := by group
      rw [heq] at this
      exact this.symm
    refine mul_mem (Subgroup.mem_sup_left hj) (Subgroup.mem_sup_right (mul_mem
      (Subgroup.mem_sup_left ⟨hk, hkC⟩) (Subgroup.mem_sup_right ⟨he, heN⟩)))
  · refine sup_le ?_ (sup_le ?_ ?_)
    · rw [Subgroup.zpowers_le]
      exact ⟨hJN, h.J_mem_H⟩
    · rintro x ⟨hxK, hxC⟩
      exact ⟨Subgroup.centralizer_le_normalizer _ hxC, h.K_le_H hxK⟩
    · rintro x ⟨hxE, hxN⟩
      exact ⟨hxN, fr.E_le_H hxE⟩

@[expose] noncomputable def fieldAction (e' : h.K ≃* PSL(2, GaloisField h.p h.f)) :
    fr.E →* MulAut PSL(2, GaloisField h.p h.f) :=
  (PSL2Sub.conjHom e').comp (Subgroup.inclusion fr.E_le_normalizer_K)

theorem emb_fieldAction (e' : h.K ≃* PSL(2, GaloisField h.p h.f)) (x : fr.E)
    (y : PSL(2, GaloisField h.p h.f)) :
    psl2Emb e' (fr.fieldAction e' x y) = x * psl2Emb e' y * (x : G)⁻¹ :=
  PSL2Sub.emb_conjHom e' _ y

theorem ker_fieldAction (e' : h.K ≃* PSL(2, GaloisField h.p h.f)) :
    (fr.fieldAction e').ker = h.F.subgroupOf fr.E := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← fr.E_inf_centralizer_K]
  constructor
  · intro hx
    refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
    obtain ⟨y, rfl⟩ := PSL2Sub.exists_emb_eq e' hk
    have h1 := congrArg (psl2Emb e') (DFunLike.congr_fun hx y)
    rw [emb_fieldAction] at h1
    change (x : G) * psl2Emb e' y * (x : G)⁻¹ = psl2Emb e' y at h1
    calc psl2Emb e' y * x = ((x : G) * psl2Emb e' y * (x : G)⁻¹) * x := by rw [h1]
      _ = x * psl2Emb e' y := by group
  · rintro ⟨-, hxC⟩
    ext y
    apply PSL2Sub.emb_injective e'
    rw [emb_fieldAction, MulAut.one_apply,
      ← Subgroup.mem_centralizer_iff.mp hxC _ (PSL2Sub.emb_mem e' y), mul_inv_cancel_right]

theorem exists_fieldAut_of_le_E
    {X : Subgroup G} (hXE : X ≤ fr.E) :
    ∃ (e' : h.K ≃* PSL(2, GaloisField h.p h.f)) (σ₀ : GaloisField h.p h.f ≃+* GaloisField h.p h.f),
      orderOf σ₀ = h.eX X ∧ Odd (orderOf σ₀) ∧
      ∀ y, psl2Emb e' y ∈ Subgroup.centralizer (X : Set G) ↔ psl2FieldAut _ σ₀ y = y := by
  classical
  obtain ⟨e', P₀, hT⟩ := fr.exists_coords
  set F := GaloisField h.p h.f
  set ψ := fr.fieldAction e'
  set φ := psl2FieldAut F
  have hφinj : Function.Injective φ := psl2FieldAut_injective h.odd_p h.f_pos
  have hψ : ∀ x : fr.E, ψ x ∈ φ.range := by
    intro x
    obtain ⟨σ, hσ⟩ := fr.conj_eq_fieldAut hT x.2
    refine ⟨σ, (?_ : ψ x = φ σ).symm⟩
    ext y
    apply PSL2Sub.emb_injective e'
    rw [emb_fieldAction, hσ]
  set X' := X.subgroupOf fr.E
  set Y := X'.map ψ with hYdef
  have hYle : Y ≤ φ.range := by
    rintro _ ⟨x, -, rfl⟩
    exact hψ x
  set Γ := Y.comap φ with hΓ
  have hΓY : Γ.map φ = Y := Subgroup.map_comap_eq_self hYle
  have hcardΓ : Nat.card Γ = Nat.card Y := by
    rw [← hΓY, Subgroup.card_map_of_injective hφinj]
  have : IsCyclic (F ≃+* F) := isCyclic_ringEquiv_galoisField
  have : IsCyclic Γ := Subgroup.isCyclic_of_le (le_top : Γ ≤ ⊤)
  obtain ⟨⟨σ₀, hσ₀Γ⟩, hgen⟩ := IsCyclic.exists_generator (α := Γ)
  have hΓeq : Γ = Subgroup.zpowers σ₀ := by
    apply le_antisymm
    · intro τ hτ
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨τ, hτ⟩)
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    · rw [Subgroup.zpowers_le]
      exact hσ₀Γ
  have hord : orderOf σ₀ = Nat.card Y := by
    rw [← hcardΓ, hΓeq, Nat.card_zpowers]
  have hker := fr.ker_fieldAction e'
  have hFE : h.F ≤ fr.E := fr.F_le_E
  have hXFE : X ⊔ h.F ≤ fr.E := sup_le hXE hFE
  have hYe : Nat.card Y = h.eX X := by
    have hZ := card_eq_card_map_mul_card_inf_ker ψ ((X ⊔ h.F).subgroupOf fr.E)
    have hZmap : ((X ⊔ h.F).subgroupOf fr.E).map ψ = Y := by
      rw [Subgroup.subgroupOf_sup hXE hFE, Subgroup.map_sup]
      have : (h.F.subgroupOf fr.E).map ψ = ⊥ := by
        rw [Subgroup.map_eq_bot_iff, ← hker]
      rw [this, sup_bot_eq]
    have hZker : (X ⊔ h.F).subgroupOf fr.E ⊓ ψ.ker = h.F.subgroupOf fr.E := by
      rw [hker]
      exact inf_eq_right.mpr fun x hx =>
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx))
    rw [hZmap, hZker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXFE).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFE).toEquiv] at hZ
    rw [Hyp.eX, hZ, Nat.mul_div_cancel _ Nat.card_pos]
  have hodd : Odd (Nat.card Y) := by
    have h1 : Nat.card Y ∣ Nat.card X' := Subgroup.card_map_dvd X' ψ
    have h2 : Nat.card X' ∣ Nat.card fr.E := Subgroup.card_subgroup_dvd_card X'
    exact Odd.of_dvd_nat fr.odd_card_E (h1.trans h2)
  refine ⟨e', σ₀, hord.trans hYe, hord ▸ hodd, fun y => ?_⟩
  have hfixψ : ∀ x : fr.E, ψ x y = y ↔ (x : G) * psl2Emb e' y = psl2Emb e' y * x := by
    intro x
    constructor
    · intro hx
      have h1 := congrArg (psl2Emb e') hx
      rw [emb_fieldAction] at h1
      calc (x : G) * psl2Emb e' y = ((x : G) * psl2Emb e' y * (x : G)⁻¹) * x := by group
        _ = psl2Emb e' y * x := by rw [h1]
    · intro hx
      apply PSL2Sub.emb_injective e'
      rw [emb_fieldAction, hx, mul_inv_cancel_right]
  constructor
  · intro hyC
    obtain ⟨x, hxX, hxσ⟩ : φ σ₀ ∈ Y := hσ₀Γ
    rw [← hxσ]
    exact (hfixψ x).mpr (Subgroup.mem_centralizer_iff.mp hyC (x : G)
      (Subgroup.mem_subgroupOf.mp hxX))
  · intro hfix
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxY : ψ ⟨x, hXE hx⟩ ∈ Y := ⟨⟨x, hXE hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    obtain ⟨τ, hτ⟩ := hYle hxY
    have hτΓ : τ ∈ Γ := by
      change φ τ ∈ Y
      rw [hτ]
      exact hxY
    rw [hΓeq] at hτΓ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτΓ
    have hle : Subgroup.zpowers (φ σ₀) ≤ MulAction.stabilizer (MulAut PSL(2, F)) y := by
      rw [Subgroup.zpowers_le]
      exact hfix
    have hk : (φ σ₀) ^ k ∈ MulAction.stabilizer (MulAut PSL(2, F)) y :=
      hle (Subgroup.zpow_mem_zpowers _ k)
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, ← map_zpow, hτ] at hk
    exact (hfixψ ⟨x, hXE hx⟩).mp hk

theorem eX_dvd_and_KX_iso
    {X : Subgroup G} (hXE : X ≤ fr.E) :
    h.eX X ∣ h.f ∧ Nonempty (h.KX X ≃* PSL(2, GaloisField h.p (h.f / h.eX X))) := by
  obtain ⟨e', σ₀, hord, hodd, hC⟩ := fr.exists_fieldAut_of_le_E hXE
  set K₀ := GaloisField h.p h.f
  obtain ⟨hdvd, hcard⟩ := card_fixedSubfield_galoisField h.f_pos.ne' σ₀
  rw [hord] at hdvd hcard
  refine ⟨hdvd, ?_⟩
  set F0 := FixedPoints.subfield (Subgroup.zpowers σ₀) K₀ with hF0
  have hKX : h.KX X = ((psl2Map F0.subtype).range).map (psl2Emb e') := by
    ext x
    constructor
    · rintro ⟨hxK, hxC⟩
      obtain ⟨y, rfl⟩ := PSL2Sub.exists_emb_eq e' hxK
      have hfix := (hC y).mp hxC
      rw [psl2FieldAut_eq_psl2Map] at hfix
      exact ⟨y, (psl2Map_eq_self_iff σ₀ hodd y).mp hfix, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨PSL2Sub.emb_mem e' y, (hC y).mpr ?_⟩
      rw [psl2FieldAut_eq_psl2Map]
      exact (psl2Map_eq_self_iff σ₀ hodd y).mpr hy
  have hfe : h.f / h.eX X ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd h.f_pos hdvd) (hord ▸ hodd.pos)).ne'
  have : Fintype F0 := Fintype.ofFinite F0
  have : Fintype (GaloisField h.p (h.f / h.eX X)) := Fintype.ofFinite _
  let e3 : F0 ≃+* GaloisField h.p (h.f / h.eX X) := FiniteField.ringEquivOfCardEq (by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hcard, GaloisField.card _ _ hfe])
  let e1 : h.KX X ≃* (psl2Map F0.subtype).range :=
    (MulEquiv.subgroupCongr hKX).trans
      (((psl2Map F0.subtype).range).equivMapOfInjective _ (PSL2Sub.emb_injective e')).symm
  let e2 : (psl2Map F0.subtype).range ≃* PSL(2, F0) :=
    (MonoidHom.ofInjective (psl2Map_injective _)).symm
  exact ⟨e1.trans (e2.trans (psl2RingEquiv e3))⟩

end Frame

theorem lemma_2_6_i : S_lemma_2_6_i := by
  intro G _ _ h fr X hXE _
  obtain ⟨h1, h2⟩ := fr.eX_dvd_and_KX_iso hXE
  exact ⟨h1, h2, fr.normalizer_inf_H_eq hXE⟩

theorem lemma_2_6_cover :
    ∀ (G : Type) [Group G] [Finite G] (h : Hyp G) (fr : Frame h),
      (∀ N : Subgroup G, N.Normal → N.index ≠ 2) →
      Subgroup.normalizer ((fr.S : Subgroup G) : Set G) =
        (Subgroup.normalizer ((fr.S : Subgroup G) : Set G) ⊓
          Subgroup.centralizer (fr.E : Set G)) ⊔ fr.CS := by
  intro G _ _ h fr hidx
  exact fr.normalizer_S_eq hidx

end CFSG.Walter.W67
