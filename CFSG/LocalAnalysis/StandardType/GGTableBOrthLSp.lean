module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthLD4
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorus
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMoreSp

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly SpCoord Multiplicative

namespace TableBOrthL

section Line

variable {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}

theorem ggNoInvariantLineSC_of_signedEltSC [Finite R] (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (h : GGTorusSignedEltSC p R) : CorFourTwoOpen.GGNoInvariantLineSC p R I := by
  intro Eh hEhI hEhA h3 hscR Λ hΛ hΛp
  have := TableBSymp.finite_mulAut (R := R)
  have hinj := OrthRest.conj_injective hZ
  set E := Eh.comap (MulAut.conj : R →* MulAut R) with hE
  have hmap : E.map (MulAut.conj : R →* MulAut R) = Eh := by
    rw [hE, Subgroup.map_comap_eq, inf_eq_right.mpr]
    intro φ hφ
    exact hI (hEhI hφ)
  have hcardE : Nat.card E = Nat.card Eh := by
    rw [Nat.card_congr (E.equivMapOfInjective _ hinj).toEquiv, hmap]
  have hEe : IsElemAbelian p E := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hEhA a.2 b.2
    · rw [map_pow, map_one]
      exact hEhA.2 _ hx
  have hscE : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    show MulAut.conj g ∈ Eh
    refine hscR g (fun a ha => ?_) hgp
    obtain ⟨y, rfl⟩ := hI (hEhI ha)
    have hy : y ∈ E := ha
    rw [MulAut.conj_apply, ← hg y hy, mul_inv_cancel_right]
  obtain ⟨k, τ, hτinj, hτE, hsgn, hperm, -⟩ := h E hEe (hcardE ▸ h3) hscE
  set Λ' := Λ.comap (MulAut.conj : R →* MulAut R) with hΛ'
  have hΛmap : Λ'.map (MulAut.conj : R →* MulAut R) = Λ := by
    rw [hΛ', Subgroup.map_comap_eq, inf_eq_right.mpr]
    intro φ hφ
    exact hI (hEhI (hΛ hφ))
  have hΛ'card : Nat.card Λ' = p := by
    rw [Nat.card_congr (Λ'.equivMapOfInjective _ hinj).toEquiv, hΛmap, hΛp]
  have hΛ'E : Λ' ≤ E := fun e he => hΛ he
  by_contra hcon
  push Not at hcon
  have hinv : ∀ w : R, (∀ f, ∃ f', w * τ f * w⁻¹ = τ f') → ∀ e ∈ Λ', w * e * w⁻¹ ∈ Λ' := by
    intro w hw e he
    have hwN : MulAut.conj w ∈ Subgroup.normalizer (Eh : Set (MulAut R)) := by
      refine NbrLang.mem_normalizer_of_conj_mem fun b hb => ?_
      obtain ⟨y, rfl⟩ := hI (hEhI hb)
      have hy : y ∈ E := hb
      rw [← hτE] at hy
      obtain ⟨f, rfl⟩ := hy
      obtain ⟨f', hf'⟩ := hw f
      rw [← map_inv, ← map_mul, ← map_mul, hf']
      show τ f' ∈ E
      rw [← hτE]
      exact ⟨f', rfl⟩
    have h1 := hcon w hwN (MulAut.conj e) he
    show MulAut.conj (w * e * w⁻¹) ∈ Λ
    rw [map_mul, map_mul, map_inv]
    exact h1
  rcases NbrSp.eq_bot_or_eq_top_of_signed hp hp2 (Λ'.comap τ)
      (fun i f hf => by
        obtain ⟨w, hw⟩ := hsgn i
        have e1 := hw f
        rw [sgnAut_apply] at e1
        show τ (Function.update f i (f i)⁻¹) ∈ Λ'
        rw [← e1]
        exact hinv w (fun f => ⟨_, hw f⟩) _ hf)
      (fun σ f hf => by
        obtain ⟨w, hw⟩ := hperm σ
        have e1 := hw f
        rw [permAut_apply] at e1
        show τ (f ∘ ⇑σ⁻¹) ∈ Λ'
        rw [← e1]
        exact hinv w (fun f => ⟨_, hw f⟩) _ hf) with hbot | htop
  · have h1 : Λ' = ⊥ := by
      rw [← Subgroup.map_comap_eq_self (hΛ'E.trans hτE.ge), hbot, Subgroup.map_bot]
    rw [h1, Subgroup.card_bot] at hΛ'card
    exact hp.one_lt.ne hΛ'card
  · have h1 : E ≤ Λ' := by
      rw [← hτE]
      rintro _ ⟨f, rfl⟩
      exact (htop ▸ Subgroup.mem_top f : f ∈ Λ'.comap τ)
    have h2 := Subgroup.card_le_of_le h1
    rw [hcardE, hΛ'card] at h2
    have h4 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    rw [pow_one] at h4
    omega

end Line

section Signed

variable {p k : ℕ}

theorem eq_self_of_signed_unipotent (hp : p.Prime) (hp2 : p ≠ 2)
    {u : (Fin k → Multiplicative (ZMod p)) → Fin k → Multiplicative (ZMod p)}
    {π : Equiv.Perm (Fin k)} {ε : Fin k → ZMod p} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i))
    (h2 : ∀ f, u (f⁻¹ * u f) = f⁻¹ * u f) (f : Fin k → Multiplicative (ZMod p)) : u f = f := by
  have key : ∀ j, π j = j ∧ ε j = 1 := by
    intro j
    set δ : Fin k → Multiplicative (ZMod p) := Pi.mulSingle j (ofAdd 1) with hδ
    have hδj : toAdd (δ j) = 1 := by simp [hδ]
    have hδo : ∀ i, i ≠ j → toAdd (δ i) = 0 := fun i hi => by
      simp [hδ, Pi.mulSingle_eq_of_ne hi]
    have hgx : ∀ x, toAdd ((δ⁻¹ * u δ) x) = - toAdd (δ x) + toAdd (u δ x) := fun x => by
      rw [toAdd_mul_apply, toAdd_inv_apply]
    have huδ : toAdd (u δ (π j)) = ε j := by rw [hu δ j, hδj, mul_one]
    have hfix : toAdd ((δ⁻¹ * u δ) (π j)) = ε j * toAdd ((δ⁻¹ * u δ) j) := by
      have h3 := hu (δ⁻¹ * u δ) j
      rwa [h2 δ] at h3
    by_cases hπ : π j = j
    · refine ⟨hπ, ?_⟩
      have huδ' : toAdd (u δ j) = ε j := by
        have h4 := huδ
        rwa [hπ] at h4
      have e1 : toAdd ((δ⁻¹ * u δ) j) = -1 + ε j := by rw [hgx, hδj, huδ']
      have e2 : toAdd ((δ⁻¹ * u δ) (π j)) = -1 + ε j := by rw [hπ]; exact e1
      rw [e2, e1] at hfix
      have hε2 : ε j * ε j = 1 := coord_sign_mul_self (hε j)
      have h5 : ε j - 1 = -(ε j - 1) := by linear_combination hfix + hε2
      exact sub_eq_zero.mp (coord_eq_zero_of_eq_neg hp hp2 h5)
    · exfalso
      have hππ : π (π⁻¹ j) = j := by rw [Equiv.Perm.coe_inv, Equiv.apply_symm_apply]
      have hj' : π⁻¹ j ≠ j := fun h => hπ (by
        have h4 := congrArg π h
        rwa [hππ, eq_comm] at h4)
      have e1 : toAdd ((δ⁻¹ * u δ) j) = -1 := by
        have h4 := hu δ (π⁻¹ j)
        rw [hππ, hδo _ hj', mul_zero] at h4
        rw [hgx, hδj, h4, add_zero]
      have e2 : toAdd ((δ⁻¹ * u δ) (π j)) = ε j := by
        rw [hgx, hδo _ hπ, huδ, neg_zero, zero_add]
      rw [e1, e2] at hfix
      have h5 : ε j = -ε j := by linear_combination hfix
      exact coord_sign_ne_zero hp (hε j) (coord_eq_zero_of_eq_neg hp hp2 h5)
  funext x
  have hx := hu f x
  obtain ⟨hπx, hεx⟩ := key x
  rw [hπx, hεx, one_mul] at hx
  exact toAdd.injective hx

end Signed

@[expose] def GGNoTransvectionSC (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ Eh : Subgroup (MulAut R), (Eh : Set (MulAut R)) ⊆ I → IsElemAbelian p Eh →
    p ^ 3 ≤ Nat.card Eh → CorFourTwoOpen.GGTorusSelfCentR p Eh →
    ∀ a : Subgroup.normalizer (Eh : Set (MulAut R)),
      ¬ GGIsTransvection p (Eh.normalizerMonoidHom a)

section TvSigned

variable {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}

theorem ggNoTransvectionSC_of_signedEltSC [Finite R] (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hAut : ∀ α : MulAut R, α ∈ Set.range (MulAut.conj : R →* MulAut R))
    (h : GGTorusSignedEltSC p R) : GGNoTransvectionSC p R I := by
  intro Eh hEhI hEhA h3 hscR a htv
  have := TableBSymp.finite_mulAut (R := R)
  have hinj := OrthRest.conj_injective hZ
  set E := Eh.comap (MulAut.conj : R →* MulAut R) with hE
  have hmap : E.map (MulAut.conj : R →* MulAut R) = Eh := by
    rw [hE, Subgroup.map_comap_eq, inf_eq_right.mpr]
    intro φ hφ
    exact hI (hEhI hφ)
  have hcardE : Nat.card E = Nat.card Eh := by
    rw [Nat.card_congr (E.equivMapOfInjective _ hinj).toEquiv, hmap]
  have hEe : IsElemAbelian p E := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hEhA a.2 b.2
    · rw [map_pow, map_one]
      exact hEhA.2 _ hx
  have hscE : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    show MulAut.conj g ∈ Eh
    refine hscR g (fun a ha => ?_) hgp
    obtain ⟨y, rfl⟩ := hI (hEhI ha)
    have hy : y ∈ E := ha
    rw [MulAut.conj_apply, ← hg y hy, mul_inv_cancel_right]
  obtain ⟨k, τ, hτinj, hτE, -, -, hnorm⟩ := h E hEe (hcardE ▸ h3) hscE
  obtain ⟨w, hw⟩ := hAut (a : MulAut R)
  have hval : ∀ g : R, (a : MulAut R) * MulAut.conj g * (a : MulAut R)⁻¹ =
      MulAut.conj (w * g * w⁻¹) := by
    intro g
    rw [← hw, map_mul, map_mul, map_inv]
  have hwE : ∀ e ∈ E, w * e * w⁻¹ ∈ E := by
    intro e he
    show MulAut.conj (w * e * w⁻¹) ∈ Eh
    rw [← hval]
    exact (Subgroup.mem_normalizer_iff.mp a.2 (MulAut.conj e)).mp he
  obtain ⟨π, ε, hε, hact⟩ := hnorm w hwE
  have hmemτ : ∀ f, MulAut.conj (τ f) ∈ Eh := fun f => by
    have h1 : τ f ∈ E := hτE ▸ ⟨f, rfl⟩
    exact h1
  have hex : ∀ f, ∃ f', w * τ f * w⁻¹ = τ f' := by
    intro f
    have h1 : w * τ f * w⁻¹ ∈ τ.range := by
      rw [hτE]
      exact hwE _ (hmemτ f)
    obtain ⟨f', hf'⟩ := h1
    exact ⟨f', hf'.symm⟩
  choose u hu using hex
  have hψ : ∀ g, Eh.normalizerMonoidHom a ⟨MulAut.conj (τ g), hmemτ g⟩ =
      ⟨MulAut.conj (τ (u g)), hmemτ (u g)⟩ := by
    intro g
    apply Subtype.ext
    show (a : MulAut R) * MulAut.conj (τ g) * (a : MulAut R)⁻¹ = MulAut.conj (τ (u g))
    rw [hval, hu g]
  have hmul : ∀ g g', (⟨MulAut.conj (τ g), hmemτ g⟩ : Eh)⁻¹ * ⟨MulAut.conj (τ g'), hmemτ g'⟩ =
      ⟨MulAut.conj (τ (g⁻¹ * g')), hmemτ _⟩ := by
    intro g g'
    apply Subtype.ext
    show (MulAut.conj (τ g))⁻¹ * MulAut.conj (τ g') = MulAut.conj (τ (g⁻¹ * g'))
    rw [map_mul, map_mul, map_inv, map_inv]
  have h2 : ∀ f, u (f⁻¹ * u f) = f⁻¹ * u f := by
    intro f
    have e1 := htv.2 ⟨MulAut.conj (τ f), hmemτ f⟩
    rw [hψ, hmul, hψ] at e1
    exact hτinj (hinj (congrArg Subtype.val e1))
  have hid := eq_self_of_signed_unipotent hp hp2 hε (fun f i => hact f (u f) (hu f) i) h2
  have hall : ∀ e : Eh, Eh.normalizerMonoidHom a e = e := by
    rintro ⟨φ, hφ⟩
    obtain ⟨y, rfl⟩ := hI (hEhI hφ)
    have hy : y ∈ E := hφ
    rw [← hτE] at hy
    obtain ⟨f, rfl⟩ := hy
    apply Subtype.ext
    show (a : MulAut R) * MulAut.conj (τ f) * (a : MulAut R)⁻¹ = MulAut.conj (τ f)
    rw [hval, hu f, hid f]
  have hcard : Nat.card {e : Eh // Eh.normalizerMonoidHom a e = e} = Nat.card Eh :=
    Nat.card_congr (Equiv.subtypeUnivEquiv hall)
  have h1 := htv.1
  rw [hcard] at h1
  have hpos : 0 < Nat.card Eh := Nat.card_pos
  exact hp.one_lt.ne' (Nat.eq_of_mul_eq_mul_left hpos (h1.trans (mul_one _).symm))

end TvSigned

section Config

variable {G : Type} [Group G] [Finite G]

theorem mem_zpowers_of_noTransvectionSC {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hC : GGConfig p B Bs x L D J)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S) (hL : commutator L = ⊤)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hZc : GGCenterCoprime p R) (htv : GGNoTransvectionSC p R I)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced (Subgroup.centralizer ({x} : Set G)) Bs)
    (hφt : GGIsTransvection p φ) (b : ↥Bs) : ((b⁻¹ * φ b : ↥Bs) : G) ∈ Subgroup.zpowers x := by
  by_contra hb0
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hC.2.1.1.trans hBsN
  obtain ⟨-, h3', -⟩ := card_range_ggBeta_bstar hC hL θ hBN hBsN
  have hSCB : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hC.2.1.2.2.2
  obtain ⟨hT, hBs, -⟩ := hC
  obtain ⟨-, -, -, -, -, hβ, hS, -⟩ := hT
  have hp : p.Prime := hβ.1
  have := Fact.mk hp
  have : Finite R := Finite.of_equiv _ θ.toEquiv
  obtain ⟨g, hgx, hgN, hφg⟩ := hφ
  have hgL : g ∈ Subgroup.normalizer (L : Set G) := mem_normalizer_of_sstar hS hnc hgx
  have hxBs : x ∈ Bs := hBs.1 hS.2.1
  have hZ' : ¬ p ∣ Nat.card (Subgroup.center L) := by
    have h1 := hZc L (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL
    rwa [ker_ggQuotHom] at h1
  set β := ggBeta L θ hBsN with hβdef
  set a : MulAut R := ggLAut L θ ⟨g, hgL⟩ with ha
  have hconj : ∀ c : ↥Bs, a * β c * a⁻¹ = β (φ c) := by
    intro c
    rw [ggBeta_eq, ggBeta_eq, ha, ggLAut_conj]
    congr 1
    apply Subtype.ext
    exact (hφg c).symm
  have hNa : a ∈ Subgroup.normalizer ((β.range : Subgroup (MulAut R)) : Set (MulAut R)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨φ c, (hconj c).symm⟩
    · rintro ⟨c, hc⟩
      refine ⟨φ.symm c, ?_⟩
      have h1 := hconj (φ.symm c)
      rw [MulEquiv.apply_symm_apply, hc] at h1
      exact mul_left_cancel (mul_right_cancel h1)
  have hEhI : ((β.range : Subgroup (MulAut R)) : Set (MulAut R)) ⊆ I := by
    rintro _ ⟨c, rfl⟩
    exact ggBeta_mem L θ hBsN h3 c
  have hle := Subgroup.card_le_of_le (range_ggBeta_le θ hBs.1 hBN hBsN)
  refine htv β.range hEhI (isElemAbelian_range_ggBeta θ hBs.2.1 hBsN) (h3'.trans hle)
    (CorFourTwoOpen.ggTorusSelfCentR_ggBeta hp θ hBsN hSCB hZ') ⟨a, hNa⟩ ?_
  have hkerβ : β.rangeRestrict.ker = (Subgroup.zpowers x).subgroupOf Bs := by
    rw [MonoidHom.ker_rangeRestrict]
    exact ker_ggBeta_of hp hBs.2.1 hxBs hS.2.2.1 hS.2.2.2.1.1 hS.2.2.2.2 hL θ hBsN
  have hgx' : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp hgx
  refine isTransvection_of_center_ne hp
    (fun c c' => Subtype.ext (TableB.IsElemAbelian.comm hBs.2.1 c.2 c'.2)) β.rangeRestrict
    β.rangeRestrict_surjective ?_ hφt ?_ ?_ (b := b) ?_
  · rw [hkerβ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.zpowers_le.mpr hxBs)).toEquiv, Nat.card_zpowers,
      orderOf_eq_prime (hBs.2.1.2 x hxBs) hS.2.2.1]
  · intro c hc
    rw [hkerβ, Subgroup.mem_subgroupOf] at hc
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
    apply Subtype.ext
    rw [hφg c, ← hk, (Commute.zpow_right hgx' k).eq, mul_inv_cancel_right]
  · intro c
    exact Subtype.ext (hconj c)
  · intro h1
    apply hb0
    have h2 : b⁻¹ * φ b ∈ β.rangeRestrict.ker := h1
    rw [hkerβ, Subgroup.mem_subgroupOf] at h2
    exact h2

end Config

theorem ggLTransvectionCenterInputOn_of_labelsSC {S : ℕ → LargeEvenLabel → Prop}
    (ha₀ : GGLNoncyclicInput)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => GGCenterCoprime p R ∧ GGNoTransvectionSC p R I) :
    GGLTransvectionCenterInputOn S := by
  intro G _ _ p B Bs x L D J hC hM φ hφ htv b
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBsN, h3⟩, hZc, htvt⟩ := largeEvenRawDatum_exists hraw
  exact mem_zpowers_of_noTransvectionSC hC (ha₀ G p B x L hC.1) hL θ hBsN h3 hZc htvt hφ htv b

theorem ggLTransvectionCenterInputOn_of_labelsSC_pilot {S : ℕ → LargeEvenLabel → Prop}
    (hpilot : ∀ p lab, S p lab → GGOutdiagPilotLabel lab)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => GGCenterCoprime p R ∧ GGNoTransvectionSC p R I) :
    GGLTransvectionCenterInputOn S := by
  intro G _ _ p B Bs x L D J hC hM φ hφ htv b
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  have hnc := ggLNoncyclicInputOn_pilot G p B x L hC.1 (largeEvenMarking_mono
    (fun lab _ _ _ _ _ hP => ⟨hpilot p lab hP.1, hP.2.1, hC.2.1.1.trans hP.2.2.1,
      fun b hb => hP.2.2.2 b (hC.2.1.1 hb)⟩) hM)
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBsN, h3⟩, hZc, htvt⟩ := largeEvenRawDatum_exists hraw
  exact mem_zpowers_of_noTransvectionSC hC hnc hL θ hBsN h3 hZc htvt hφ htv b

end TableBOrthL

open TableBOrthL

section Recipe

theorem recipeSymplectic_lineTvSC_two {m N : ℕ} (hm : 3 ≤ m) (hN : N = 2)
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeSymplectic m N false Q) :
    LargeEvenRecipeSymplectic m N false fun R _ I F => Q R I F ∧
      (GGCenterCoprime 3 R ∧ CorFourTwoOpen.GGNoInvariantLineSC 3 R I ∧
        GGNoTransvectionSC 3 R I) := by
  subst hN
  obtain ⟨K, _, _, hK, hQ⟩ := h
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (le_refl 1) (by rw [hK, pow_one])
  have : NeZero m := ⟨by omega⟩
  obtain ⟨hT, hcp⟩ := ggSpNonsplitTorusInput_holds K m 3 (by omega) Nat.prime_three
    (by rw [hK])
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Finite (LargeEvenProj (LargeEvenSpGroup K m)) := inferInstance
  exact ⟨CorFourTwoOpen.ggCenterCoprime_of_centerPrime hcp,
    ggNoInvariantLineSC_of_signedEltSC Nat.prime_three hp2 TableBSymp.sp_I_subset_inn
      TableBSymp.center_spProj_eq_bot hT,
    ggNoTransvectionSC_of_signedEltSC Nat.prime_three hp2 TableBSymp.sp_I_subset_inn
      TableBSymp.center_spProj_eq_bot (TwoThree.mem_range_conj_sp hK hm) hT⟩

theorem largeEvenLabelAll_lineTvSC_spTwoThree {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGSpTwoThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGCenterCoprime p R ∧
      CorFourTwoOpen.GGNoInvariantLineSC p R I ∧ GGNoTransvectionSC p R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨rfl, hn, ht⟩ := h
  dsimp only at hn ht
  subst hn
  intro Q hQ
  have hl : 3 ≤ l := by
    have h1 := hlab.2
    rcases ht with rfl | rfl <;> dsimp only at h1 <;> omega
  rcases ht with rfl | rfl <;> exact recipeSymplectic_lineTvSC_two hl (by norm_num) hQ

end Recipe

section Labels

theorem ggLNoInvariantLineInputOn_spTwoThree : GGLNoInvariantLineInputOn GGSpTwoThreeLabel :=
  CorFourTwoOpen.ggLNoInvariantLineInputOn_of_labelsSC fun _ _ _ hlab h =>
    (largeEvenLabelAll_lineTvSC_spTwoThree hlab h).mono fun _ _ _ _ hP => ⟨hP.1, hP.2.1⟩

theorem ggLTransvectionCenterInputOn_spTwoThree :
    GGLTransvectionCenterInputOn GGSpTwoThreeLabel :=
  ggLTransvectionCenterInputOn_of_labelsSC_pilot (fun _ _ h => h.pilot) fun _ _ _ hlab h =>
    (largeEvenLabelAll_lineTvSC_spTwoThree hlab h).mono fun _ _ _ _ hP => ⟨hP.1, hP.2.2⟩

end Labels

end CFSG.StandardType

end
