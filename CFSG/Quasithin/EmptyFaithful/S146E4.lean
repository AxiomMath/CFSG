module

public import CFSG.Quasithin.EmptyFaithful.S146D8
public import CFSG.Quasithin.EmptyFaithful.S146E3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom
open scoped commutatorElement

section SecRho

variable {G : Type} [Group G] {Z U X : Subgroup G}

@[expose] noncomputable def secRho (hXZ : X ≤ Subgroup.normalizer (Z : Set G))
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) : ↥X →* MulAut ↥(tildeOf Z U) :=
  (conjAct (tildeOf Z U)).comp
    (((secMk (Subgroup.normalizer (Z : Set G)) Z).comp (Subgroup.inclusion hXZ)).codRestrict
      (Subgroup.normalizer (tildeOf Z U : Set (SecQuot (Subgroup.normalizer (Z : Set G)) Z)))
      (fun k => secMk_mem_normalizer_secImg (a := Subgroup.inclusion hXZ k) (hXU k.2)))

theorem secRho_coe (hXZ : X ≤ Subgroup.normalizer (Z : Set G))
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (k : ↥X) (w : ↥(tildeOf Z U)) :
    ((secRho hXZ hXU k w : ↥(tildeOf Z U)) :
        SecQuot (Subgroup.normalizer (Z : Set G)) Z) =
      secMk (Subgroup.normalizer (Z : Set G)) Z (Subgroup.inclusion hXZ k) * w *
        (secMk (Subgroup.normalizer (Z : Set G)) Z (Subgroup.inclusion hXZ k))⁻¹ :=
  conjAct_apply_coe' (tildeOf Z U) _ w

@[expose] def tildeElt (hU : U ≤ Subgroup.normalizer (Z : Set G)) (u : G) (hu : u ∈ U) :
    ↥(tildeOf Z U) :=
  ⟨secMk (Subgroup.normalizer (Z : Set G)) Z ⟨u, hU hu⟩, secMk_mem_secImg hu⟩

theorem secRho_apply_tildeElt_iff (hXZ : X ≤ Subgroup.normalizer (Z : Set G))
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (hU : U ≤ Subgroup.normalizer (Z : Set G))
    (x : ↥X) (u : G) (hu : u ∈ U) :
    secRho hXZ hXU x (tildeElt hU u hu) = tildeElt hU u hu ↔
      (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ Z := by
  constructor
  · intro h
    have h1 := congrArg
      (fun w : ↥(tildeOf Z U) => (w : SecQuot (Subgroup.normalizer (Z : Set G)) Z)) h
    simp only [secRho_coe, tildeElt] at h1
    have h2 : secMk (Subgroup.normalizer (Z : Set G)) Z (Subgroup.inclusion hXZ x) *
        secMk (Subgroup.normalizer (Z : Set G)) Z ⟨u, hU hu⟩ =
        secMk (Subgroup.normalizer (Z : Set G)) Z ⟨u, hU hu⟩ *
          secMk (Subgroup.normalizer (Z : Set G)) Z (Subgroup.inclusion hXZ x) :=
      mul_inv_eq_iff_eq_mul.mp h1
    exact commutator_mem_of_secMk_commute (A := Subgroup.normalizer (Z : Set G)) (B := Z)
      (x := Subgroup.inclusion hXZ x) (y := ⟨u, hU hu⟩) h2
  · intro h
    apply Subtype.ext
    simp only [secRho_coe, tildeElt]
    have h1 : secMk (Subgroup.normalizer (Z : Set G)) Z
        (Subgroup.inclusion hXZ x * ⟨u, hU hu⟩ * (Subgroup.inclusion hXZ x)⁻¹ * ⟨u, hU hu⟩⁻¹) = 1 :=
      secMk_eq_one_iff.mpr h
    simp only [map_mul, map_inv] at h1
    rw [mul_inv_eq_one] at h1
    exact h1

theorem commutator_mem_of_secRho_eq_one (hXZ : X ≤ Subgroup.normalizer (Z : Set G))
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (hU : U ≤ Subgroup.normalizer (Z : Set G))
    {x : ↥X} (hx : secRho hXZ hXU x = 1) {u : G} (hu : u ∈ U) :
    (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ Z := by
  rw [← secRho_apply_tildeElt_iff hXZ hXU hU x u hu, hx]
  rfl

theorem secRho_congr {Y : Subgroup G} (hXZ : X ≤ Subgroup.normalizer (Z : Set G))
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (hYZ : Y ≤ Subgroup.normalizer (Z : Set G))
    (hYU : Y ≤ Subgroup.normalizer (U : Set G)) {x : ↥X} {y : ↥Y} (h : (x : G) = y) :
    secRho hXZ hXU x = secRho hYZ hYU y := by
  ext w
  rw [secRho_coe, secRho_coe]
  have : Subgroup.inclusion hXZ x = Subgroup.inclusion hYZ y := Subtype.ext h
  rw [this]

end SecRho

section Normal

variable {G : Type} [Group G] [Finite G]

theorem mem_pCoreOf_of_commutator_mem {H K T : Subgroup G} (hK : K ∈ cComp H)
    (hs : IsSimpleGroup (KBar K)) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hT2 : IsPGroup 2 T) (hHKT : H = K ⊔ T) {c : G} (hcH : c ∈ H)
    (hc : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ pCoreOf 2 H) : c ∈ pCoreOf 2 H := by
  classical
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := hHKT ▸ le_sup_right
  set Q := pCoreOf 2 H with hQ
  have hQn : H ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 H
  set D := centralizerMod Q H K with hD
  have hcD : c ∈ D := ⟨hcH, hQn hcH, hc⟩
  have hDH : D ≤ H := centralizerMod_le_left _ _ _
  have hDnorm : H ≤ Subgroup.normalizer (D : Set G) :=
    le_normalizer_centralizerMod hQn Subgroup.le_normalizer hKn
  have hKD : ∀ x ∈ K, x ∈ D → x ∈ Q := by
    intro x hxK hxD
    have hxH : x ∈ H := hKH hxK
    have hx1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩ ∈ modO2Image H K :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxK)
    have hcomm : ∀ y ∈ modO2Image H K, QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩ * y =
        y * QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩ := by
      intro y hy
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
      have ha' : (a : G) ∈ K := Subgroup.mem_subgroupOf.mp ha
      have hxa : x * (a : G) * x⁻¹ * (a : G)⁻¹ ∈ Q := hxD.2.2 a ha'
      obtain ⟨c', hcP, hcc⟩ := Subgroup.mem_map.mp hxa
      have hcab : c' = ⟨x, hxH⟩ * a * ⟨x, hxH⟩⁻¹ * a⁻¹ := Subtype.ext (by simpa using hcc)
      have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) (⟨x, hxH⟩ * a * ⟨x, hxH⟩⁻¹ * a⁻¹) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (hcab ▸ (by exact hcP))
      simp only [map_mul, map_inv] at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp (by simpa [commutatorElement_def] using h1)
    have h2 := eq_one_of_forall_commute_modO2Image hK hs _ hx1 hcomm
    exact mem_pCoreOf_of_mem_pCore ((QuotientGroup.eq_one_iff _).mp h2)
  have hDp : IsPGroup 2 D := by
    intro d
    obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup_two hT2 (fun t ht => hKn (hTH ht))
      (hHKT ▸ hDH d.2) (x := (d : G))
    have hxD : (d : G) ^ 2 ^ k ∈ D := D.pow_mem d.2 _
    have hxQ := hKD _ hk hxD
    obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 H) ⟨_, hxQ⟩
    refine ⟨k + m, ?_⟩
    apply Subtype.ext
    have := congrArg Subtype.val hm
    simpa [pow_add, pow_mul] using this
  exact le_pCoreOf_of_le_normalizer 2 hDH hDnorm hDp hcD

end Normal

section StepB

variable {G : Type} [Group G] {K Z U₁ H : Subgroup G}

theorem Sec8.le_conjSub_of_commutator_mem (h : Sec8 K Z U₁)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) {u : G} (huU : u ∈ U₁) (huZ : u ∉ Z) {x : G}
    (hxH : x ∈ H) (hxZ : x ∈ Subgroup.normalizer (Z : Set G)) (hxu : x * u * x⁻¹ * u⁻¹ ∈ Z) :
    U₁ ≤ conjSub x U₁ := by
  have hxK : ∀ k ∈ K, x⁻¹ * k * x ∈ K := fun k hk => by
    have := (Subgroup.mem_normalizer_iff.mp (hKn (H.inv_mem hxH)) k).mp hk
    simpa using this
  have hxinvZ : ∀ z ∈ Z, x⁻¹ * z * x ∈ Z := fun z hz => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxZ) z).mp hz
    simpa using this
  set W₀ := conjSub x U₁ ⊓ U₁ with hW₀
  have hZW : Z ≤ W₀ := fun z hz => ⟨mem_conjSub.mpr (h.le (hxinvZ z hz)), h.le hz⟩
  have hKconj : K ≤ Subgroup.normalizer ((conjSub x U₁ : Subgroup G) : Set G) := by
    intro k hk
    apply mem_normalizer_of_conjSub_eq
    rw [← conjSub_mul]
    have e : k * x = x * (x⁻¹ * k * x) := by group
    rw [e, conjSub_mul, conjSub_eq_of_mem_normalizer (h.KU (hxK k hk))]
  have hKW : K ≤ Subgroup.normalizer (W₀ : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hKconj hk, h.KU hk⟩
  have huW : u ∈ W₀ := by
    refine ⟨mem_conjSub.mpr ?_, huU⟩
    have e : x⁻¹ * u * x = (x⁻¹ * (x * u * x⁻¹ * u⁻¹)⁻¹ * x) * u := by group
    rw [e]
    exact U₁.mul_mem (h.le (hxinvZ _ (Z.inv_mem hxu))) huU
  rcases h.irr W₀ hZW inf_le_right hKW with hW | hW
  · exact absurd (hW ▸ huW) huZ
  · calc U₁ = W₀ := hW.symm
      _ ≤ conjSub x U₁ := inf_le_left

theorem Sec8.mem_normalizer_of_mem_centralizerMod (h : Sec8 K Z U₁)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) {u : G} (huU : u ∈ U₁) (huZ : u ∉ Z) {x : G}
    (hx : x ∈ centralizerMod Z H (Subgroup.zpowers u)) : x ∈ Subgroup.normalizer (U₁ : Set G) := by
  have hx' : x⁻¹ ∈ centralizerMod Z H (Subgroup.zpowers u) := Subgroup.inv_mem _ hx
  have h1 := h.le_conjSub_of_commutator_mem hKn huU huZ hx.1 hx.2.1
    (hx.2.2 u (Subgroup.mem_zpowers u))
  have h2 := h.le_conjSub_of_commutator_mem hKn huU huZ hx'.1 hx'.2.1
    (hx'.2.2 u (Subgroup.mem_zpowers u))
  apply mem_normalizer_of_conjSub_eq
  refine le_antisymm ?_ h1
  have := conjSub_mono x h2
  rwa [conjSub_inv_conjSub] at this

theorem mem_centralizerMod_zpowers {X : Subgroup G} {x u : G} (hxX : x ∈ X)
    (hxZ : x ∈ Subgroup.normalizer (Z : Set G)) (hu : ∀ z ∈ Z, u * z = z * u)
    (hc : x * u * x⁻¹ * u⁻¹ ∈ Z) : x ∈ centralizerMod Z X (Subgroup.zpowers u) := by
  refine ⟨hxX, hxZ, fun w hw => ?_⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  set c := x * u * x⁻¹ * u⁻¹ with hcdef
  have hcomm : Commute c u := (hu c hc).symm
  have e1 : x * u * x⁻¹ = c * u := by rw [hcdef]; group
  have e2 : x * u ^ n * x⁻¹ * (u ^ n)⁻¹ = c ^ n := by
    calc x * u ^ n * x⁻¹ * (u ^ n)⁻¹ = (x * u * x⁻¹) ^ n * (u ^ n)⁻¹ := by rw [conj_zpow]
      _ = (c * u) ^ n * (u ^ n)⁻¹ := by rw [e1]
      _ = c ^ n := by rw [hcomm.mul_zpow]; group
  rw [e2]
  exact Subgroup.zpow_mem _ hc n

theorem acts_trivially_commutator {F E : Subgroup G} {x y : G}
    (hxF : x ∈ Subgroup.normalizer (F : Set G)) (hxE : x ∈ Subgroup.normalizer (E : Set G))
    (hyF : y ∈ Subgroup.normalizer (F : Set G)) (hyE : y ∈ Subgroup.normalizer (E : Set G))
    (hx : ∀ e ∈ E, x * e * x⁻¹ * e⁻¹ ∈ F) :
    ∀ e ∈ E, (x * y * x⁻¹ * y⁻¹) * e * (x * y * x⁻¹ * y⁻¹)⁻¹ * e⁻¹ ∈ F := by
  let X : Subgroup G := Subgroup.normalizer (F : Set G) ⊓ Subgroup.normalizer (E : Set G)
  let Tr : Subgroup G := centralizerMod F X E
  have hXn : X ≤ Subgroup.normalizer (Tr : Set G) :=
    le_normalizer_centralizerMod inf_le_left Subgroup.le_normalizer inf_le_right
  have hxTr : x ∈ Tr := ⟨⟨hxF, hxE⟩, hxF, hx⟩
  have hyX : y ∈ X := ⟨hyF, hyE⟩
  have h1 : y * x⁻¹ * y⁻¹ ∈ Tr := (Subgroup.mem_normalizer_iff.mp (hXn hyX) x⁻¹).mp (Tr.inv_mem hxTr)
  have h2 : x * (y * x⁻¹ * y⁻¹) ∈ Tr := Tr.mul_mem hxTr h1
  have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
  rw [e]
  exact h2.2.2

end StepB

section Main

variable {G : Type} [Group G] [Finite G]

theorem stage146FH2S3_proof : Stage146FH2S3 := by
  intro G _ _ T M S hB K U₁ U₂ s u hd
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hKc : K ∈ cComp (mcOf T) := hd.hK
  obtain ⟨-, hL3, hKeq, -⟩ := hd.c24
  have hsimple : IsSimpleGroup (KBar K) := (hd.c19 (mcOf T) hG).2 K hKc
  have hKn : mcOf T ≤ Subgroup.normalizer (K : Set G) := by
    rw [hKeq]
    exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _)
  have hTH : T ≤ mcOf T := hG.1.1
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  have hHKT : mcOf T = K ⊔ T := by
    rw [hKeq]
    exact hd.c23.1.2
  obtain ⟨hSec, hU₁U, -⟩ := S.sec8_of_decomp hKc hL3 hd.dec
  obtain ⟨huU, hunc⟩ : u ∈ U₁ ∧ ¬ ⁅Subgroup.zpowers u, K⁆ ≤ quasithinOmegaOneCenter T := by
    rcases hd.choice with ⟨-, huU, hunc, -⟩ | ⟨⟨t, ht, htn, -⟩, -⟩
    · exact ⟨huU, hunc⟩
    · exact absurd (hKn (hTH ht)) htn
  have huZ : u ∉ quasithinOmegaOneCenter T := by
    intro hu
    apply hunc
    exact (Subgroup.commutator_mono (Subgroup.zpowers_le.mpr hu) le_rfl).trans
      (S145.commutator_le_of_le_normalizer hSec.KZ)
  have hQK : pCoreOf 2 K ≤ pCoreOf 2 (mcOf T) :=
    A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hKc)
  have hQ' : ∀ p ∈ pCoreOf 2 K, ∀ w ∈ U₁, p * w * p⁻¹ * w⁻¹ ∈ quasithinOmegaOneCenter T :=
    fun p hp w hw => S.comm_mem_Z hG (hU₁U hw) (hQK hp)
  have h168 := relIndex_pCoreOf_of_kbarIsL3Two hL3
  have hUZ : U₁ ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := hSec.norm
  have huG : u ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hG (hU₁U huU)
  set H₂ := centralizerMod (quasithinOmegaOneCenter T) (mcOf T) (Subgroup.zpowers u) with hH₂
  have hH₂Z : H₂ ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    centralizerMod_le_normalizer _ _ _
  have hH₂U : H₂ ≤ Subgroup.normalizer (U₁ : Set G) := fun x hx =>
    hSec.mem_normalizer_of_mem_centralizerMod hKn huU huZ hx
  have hel := hSec.isElemAbelian_tilde
  have hcomm : ∀ a b : ↥(tildeOf (quasithinOmegaOneCenter T) U₁), a * b = b * a :=
    fun a b => Subtype.ext (isElemAbelian_comm hel a.2 b.2)
  have hsq : ∀ a : ↥(tildeOf (quasithinOmegaOneCenter T) U₁), a ^ 2 = 1 := fun a =>
    Subtype.ext (by simpa [pow_two] using isElemAbelian_pow_eq_one hel a.2)
  set ut := tildeElt hUZ u huU with hut_def
  have hut : ut ≠ 1 := by
    intro h
    apply huZ
    have h1 := congrArg
      (fun w : ↥(tildeOf (quasithinOmegaOneCenter T) U₁) =>
        (w : SecQuot (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
          (quasithinOmegaOneCenter T))) h
    exact secMk_eq_one_iff.mp (by simpa [hut_def, tildeElt] using h1)
  let A : Subgroup (MulAut ↥(tildeOf (quasithinOmegaOneCenter T) U₁)) :=
    MulAction.stabilizer (MulAut ↥(tildeOf (quasithinOmegaOneCenter T) U₁)) ut
  have hA : ∀ σ : MulAut ↥(tildeOf (quasithinOmegaOneCenter T) U₁), σ ∈ A ↔ σ ut = ut :=
    fun σ => by simp [A, MulAction.mem_stabilizer_iff, MulAut.smul_def]
  obtain ⟨Θ₀, hΘs, hΘk⟩ := L3Stab.exists_theta_of_stabilizer hcomm hsq hSec.card_tilde hut A hA
  have hρ₂A : ∀ x : ↥H₂, secRho hH₂Z hH₂U x ∈ A := fun x =>
    (hA _).mpr ((secRho_apply_tildeElt_iff hH₂Z hH₂U hUZ x u huU).mpr
      (x.2.2.2 u (Subgroup.mem_zpowers u)))
  let ρ₂' : ↥H₂ →* ↥A := (secRho hH₂Z hH₂U).codRestrict A hρ₂A
  refine nonempty_oTwoQuot_equiv_perm_three H₂ (Θ₀.comp ρ₂') ?_ ?_
  · intro π
    obtain ⟨σ, hσ⟩ := hΘs π
    obtain ⟨k, hk⟩ := hSec.exists_rho_eq hsimple hQ' h168 σ.1
    have hkfix : hSec.rho k ut = ut := by rw [hk]; exact (hA σ.1).mp σ.2
    have hkc : (k : G) * u * (k : G)⁻¹ * u⁻¹ ∈ quasithinOmegaOneCenter T :=
      (secRho_apply_tildeElt_iff hSec.KZ hSec.KU hUZ k u huU).mp hkfix
    have hkH₂ : (k : G) ∈ H₂ := mem_centralizerMod_zpowers (le_of_mem_cComp hKc k.2)
      (hSec.KZ k.2) (fun z hz => S146T.comm_Z huG hz) hkc
    refine ⟨⟨k, hkH₂⟩, ?_⟩
    have h1 : ρ₂' ⟨k, hkH₂⟩ = σ := by
      apply Subtype.ext
      show secRho hH₂Z hH₂U ⟨k, hkH₂⟩ = σ.1
      rw [← hk]
      exact secRho_congr hH₂Z hH₂U hSec.KZ hSec.KU (rfl : ((⟨k, hkH₂⟩ : ↥H₂) : G) = k)
    show Θ₀ (ρ₂' ⟨k, hkH₂⟩) = π
    rw [h1, hσ]
  · intro x hx
    have h1 := hΘk (ρ₂' x) hx
    have h2 : secRho hH₂Z hH₂U (x * x) = 1 := by
      rw [map_mul]
      exact h1
    have hyH : ((x * x : ↥H₂) : G) ∈ mcOf T := (centralizerMod_le_left _ _ _) (x * x).2
    have hyQ : ((x * x : ↥H₂) : G) ∈ pCoreOf 2 (mcOf T) := by
      refine mem_pCoreOf_of_commutator_mem hKc hsimple hKn hT2 hHKT hyH fun k hk => ?_
      have hkH : (k : G) ∈ mcOf T := le_of_mem_cComp hKc hk
      have htriv := acts_trivially_commutator
        (hH₂Z (x * x).2) (hH₂U (x * x).2) (hSec.KZ hk) (hSec.KU hk)
        (fun w hw => commutator_mem_of_secRho_eq_one hH₂Z hH₂U hUZ h2 hw)
      have hcK : ((x * x : ↥H₂) : G) * k * ((x * x : ↥H₂) : G)⁻¹ * k⁻¹ ∈ K := by
        have h3 := (Subgroup.mem_normalizer_iff.mp (hKn hyH) k).mp hk
        exact K.mul_mem h3 (K.inv_mem hk)
      have hcen : ((x * x : ↥H₂) : G) * k * ((x * x : ↥H₂) : G)⁻¹ * k⁻¹ ∈
          centralizerMod (quasithinOmegaOneCenter T) K U₁ :=
        ⟨hcK, hSec.KZ hcK, htriv⟩
      exact hQK (hSec.centralizerMod_le hsimple hQ' hcen)
    obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 (mcOf T)) ⟨_, hyQ⟩
    refine ⟨m + 1, ?_⟩
    apply Subtype.ext
    have h4 := congrArg Subtype.val hm
    have h5 : ((x : ↥H₂) : G) ^ 2 ^ (m + 1) = (((x * x : ↥H₂) : G)) ^ 2 ^ m := by
      have e : ((x * x : ↥H₂) : G) = ((x : ↥H₂) : G) ^ 2 := by simp [pow_two]
      rw [e, ← pow_mul, ← pow_succ']
    simpa [h5] using h4

end Main

end CFSG.Quasithin
