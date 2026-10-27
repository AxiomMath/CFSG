module

public import CFSG.Quasithin.EmptyFaithful.Der6CMod
public import CFSG.Quasithin.Background.F9Section
public import CFSG.Quasithin.EmptyFaithful.S146B0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Der6C

section Action

variable (Z U₁ : Subgroup G)

abbrev NN : Subgroup G := Subgroup.normalizer (Z : Set G) ⊓ Subgroup.normalizer (U₁ : Set G)

@[expose] noncomputable def rhoN : ↥(NN Z U₁) →* MulAut ↥(tildeOf Z U₁) :=
  (conjAct (tildeOf Z U₁)).comp
    (((secMk (Subgroup.normalizer (Z : Set G)) Z).comp
        (Subgroup.inclusion (inf_le_left : NN Z U₁ ≤ Subgroup.normalizer (Z : Set G)))).codRestrict
      (Subgroup.normalizer (tildeOf Z U₁ : Set (SecQuot (Subgroup.normalizer (Z : Set G)) Z)))
      (fun k => secMk_mem_normalizer_secImg
        (a := Subgroup.inclusion (inf_le_left : NN Z U₁ ≤ Subgroup.normalizer (Z : Set G)) k)
        k.2.2))

theorem rhoN_coe (g : ↥(NN Z U₁)) (w : ↥(tildeOf Z U₁)) :
    ((rhoN Z U₁ g w : ↥(tildeOf Z U₁)) : SecQuot (Subgroup.normalizer (Z : Set G)) Z) =
      secMk (Subgroup.normalizer (Z : Set G)) Z (Subgroup.inclusion inf_le_left g) * w *
        (secMk (Subgroup.normalizer (Z : Set G)) Z (Subgroup.inclusion inf_le_left g))⁻¹ :=
  conjAct_apply_coe' (tildeOf Z U₁) _ w

variable {Z U₁}

@[expose] def wOf (hUN : U₁ ≤ Subgroup.normalizer (Z : Set G)) {u : G} (hu : u ∈ U₁) :
    ↥(tildeOf Z U₁) :=
  ⟨secMk (Subgroup.normalizer (Z : Set G)) Z ⟨u, hUN hu⟩,
    secMk_mem_secImg (x := ⟨u, hUN hu⟩) hu⟩

theorem exists_wOf (hUN : U₁ ≤ Subgroup.normalizer (Z : Set G)) (w : ↥(tildeOf Z U₁)) :
    ∃ (u : G) (hu : u ∈ U₁), wOf hUN hu = w := by
  obtain ⟨x, hx, hxw⟩ := mem_secImg.mp w.2
  exact ⟨x, hx, Subtype.ext hxw⟩

theorem rhoN_wOf_eq_iff (hUN : U₁ ≤ Subgroup.normalizer (Z : Set G)) {g : G}
    (hg : g ∈ NN Z U₁) {u : G} (hu : u ∈ U₁) :
    rhoN Z U₁ ⟨g, hg⟩ (wOf hUN hu) = wOf hUN hu ↔ g * u * g⁻¹ * u⁻¹ ∈ Z := by
  constructor
  · intro h
    have h1 := congrArg (fun a : ↥(tildeOf Z U₁) =>
      (a : SecQuot (Subgroup.normalizer (Z : Set G)) Z)) h
    simp only [rhoN_coe] at h1
    have h2 := mul_inv_eq_iff_eq_mul.mp h1
    exact commutator_mem_of_secMk_commute (A := Subgroup.normalizer (Z : Set G)) (B := Z)
      (x := Subgroup.inclusion inf_le_left ⟨g, hg⟩) (y := ⟨u, hUN hu⟩) h2
  · intro h
    apply Subtype.ext
    rw [rhoN_coe]
    have h2 := secMk_comm_of_commutator_mem (A := Subgroup.normalizer (Z : Set G)) (K := Z)
      (x := Subgroup.inclusion inf_le_left ⟨g, hg⟩) (y := ⟨u, hUN hu⟩) h
    exact mul_inv_eq_iff_eq_mul.mpr h2

theorem wOf_congr (hUN : U₁ ≤ Subgroup.normalizer (Z : Set G)) {u v : G} (hu : u ∈ U₁)
    (hv : v ∈ U₁) (h : u = v) : wOf hUN hu = wOf hUN hv := by
  subst h
  rfl

theorem wOf_mul (hUN : U₁ ≤ Subgroup.normalizer (Z : Set G)) {u v : G} (hu : u ∈ U₁)
    (hv : v ∈ U₁) : wOf hUN (U₁.mul_mem hu hv) = wOf hUN hu * wOf hUN hv := by
  apply Subtype.ext
  show secMk (Subgroup.normalizer (Z : Set G)) Z ⟨u * v, hUN (U₁.mul_mem hu hv)⟩ =
    secMk (Subgroup.normalizer (Z : Set G)) Z ⟨u, hUN hu⟩ *
      secMk (Subgroup.normalizer (Z : Set G)) Z ⟨v, hUN hv⟩
  rw [← map_mul]
  rfl

theorem wOf_inv (hUN : U₁ ≤ Subgroup.normalizer (Z : Set G)) {u : G} (hu : u ∈ U₁) :
    wOf hUN (U₁.inv_mem hu) = (wOf hUN hu)⁻¹ := by
  apply Subtype.ext
  show secMk (Subgroup.normalizer (Z : Set G)) Z ⟨u⁻¹, hUN (U₁.inv_mem hu)⟩ =
    (secMk (Subgroup.normalizer (Z : Set G)) Z ⟨u, hUN hu⟩)⁻¹
  rw [← map_inv]
  rfl

theorem wOf_eq_one (hUN : U₁ ≤ Subgroup.normalizer (Z : Set G)) {z : G} (hz : z ∈ Z)
    (hzU : z ∈ U₁) : wOf hUN hzU = 1 :=
  Subtype.ext (secMk_eq_one_iff.mpr hz)

theorem rhoN_wOf (hUN : U₁ ≤ Subgroup.normalizer (Z : Set G)) {g : G} (hg : g ∈ NN Z U₁)
    {u : G} (hu : u ∈ U₁) (hgu : g * u * g⁻¹ ∈ U₁) :
    rhoN Z U₁ ⟨g, hg⟩ (wOf hUN hu) = wOf hUN hgu := by
  apply Subtype.ext
  rw [rhoN_coe]
  show secMk (Subgroup.normalizer (Z : Set G)) Z ⟨g, hg.1⟩ *
      secMk (Subgroup.normalizer (Z : Set G)) Z ⟨u, hUN hu⟩ *
        (secMk (Subgroup.normalizer (Z : Set G)) Z ⟨g, hg.1⟩)⁻¹ =
    secMk (Subgroup.normalizer (Z : Set G)) Z ⟨g * u * g⁻¹, hUN hgu⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

end Action

section Main

variable [Finite G] {K P Z U₁ : Subgroup G}

omit [Finite G] in
theorem card_tilde (hZU : Z ≤ U₁) (hUN : U₁ ≤ Subgroup.normalizer (Z : Set G)) :
    Nat.card ↥(tildeOf Z U₁) = Z.relIndex U₁ := by
  have h1 := relIndex_secImg (A := Subgroup.normalizer (Z : Set G)) (B := Z) (le_refl Z) hZU hUN
  have h2 : secImg (Subgroup.normalizer (Z : Set G)) Z Z = ⊥ := tildeOf_eq_bot_of_le le_rfl
  rw [h2, Subgroup.relIndex_bot_left] at h1
  exact h1

omit [Finite G] in
theorem le_normalizer_of_commutator_sup (hperf : ⁅U₁, K⁆ ⊔ Z = U₁) :
    K ≤ Subgroup.normalizer (U₁ : Set G) := by
  have key : ∀ k ∈ K, ∀ u ∈ U₁, k * u * k⁻¹ ∈ U₁ := by
    intro k hk u hu
    have h1 : u * k * u⁻¹ * k⁻¹ ∈ U₁ := by
      rw [← hperf]
      exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hu hk)
    have h2 : (u * k * u⁻¹ * k⁻¹)⁻¹ * u ∈ U₁ := U₁.mul_mem (U₁.inv_mem h1) hu
    have e : (u * k * u⁻¹ * k⁻¹)⁻¹ * u = k * u * k⁻¹ := by group
    rwa [e] at h2
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key k hk x hx, fun hx => ?_⟩
  have h1 := key k⁻¹ (K.inv_mem hk) _ hx
  have e : k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x := by group
  rwa [e] at h1

theorem exists_fixed_not_centralized_of_asI231A6 (hI : AsI231A6)
    (hZU : Z ≤ U₁) (hUN : U₁ ≤ Subgroup.normalizer (Z : Set G))
    (hsq : ∀ a ∈ U₁, a ^ 2 ∈ Z) (hcomm : ∀ a ∈ U₁, ∀ b ∈ U₁, a * b * a⁻¹ * b⁻¹ ∈ Z)
    (hKZ : K ≤ Subgroup.normalizer (Z : Set G)) (hKU : K ≤ Subgroup.normalizer (U₁ : Set G))
    (hPZ : P ≤ Subgroup.normalizer (Z : Set G)) (hPU : P ≤ Subgroup.normalizer (U₁ : Set G))
    (hPK : P ≤ Subgroup.normalizer (K : Set G)) (hP2 : IsPGroup 2 P)
    (hcard : Z.relIndex U₁ = 2 ^ 5) (hperf : ⁅U₁, K⁆ ⊔ Z = U₁)
    (hQ : ∀ q ∈ pCoreOf 2 K, ∀ u ∈ U₁, q * u * q⁻¹ * u⁻¹ ∈ Z) (hA : KbarIsA6 K) :
    ∃ u ∈ U₁, (∃ k ∈ K, k * u * k⁻¹ * u⁻¹ ∉ Z) ∧ ∀ p ∈ P, p * u * p⁻¹ * u⁻¹ ∈ Z := by
  classical
  have hel : IsElemAbelian 2 (tildeOf Z U₁) := isElemAbelian_secImg_normalizer hcomm hsq
  let _ : CommGroup ↥(tildeOf Z U₁) := commGroupOfElemAbelian hel
  have hKN : K ≤ NN Z U₁ := le_inf hKZ hKU
  have hPN : P ≤ NN Z U₁ := le_inf hPZ hPU
  set ψK : ↥K →* MulAut ↥(tildeOf Z U₁) := (rhoN Z U₁).comp (Subgroup.inclusion hKN) with hψK
  set ψP : ↥P →* MulAut ↥(tildeOf Z U₁) := (rhoN Z U₁).comp (Subgroup.inclusion hPN) with hψP
  have hW2 : ∀ w : ↥(tildeOf Z U₁), w ^ 2 = 1 := fun a =>
    Subtype.ext (by simpa [pow_two] using isElemAbelian_pow_eq_one hel a.2)
  have hWcard : Nat.card ↥(tildeOf Z U₁) = 2 ^ 5 := by
    rw [card_tilde hZU hUN, hcard]
  have hconjU : ∀ k ∈ K, ∀ u ∈ U₁, k * u * k⁻¹ ∈ U₁ := fun k hk u hu =>
    (Subgroup.mem_normalizer_iff.mp (hKU hk) u).mp hu
  have hcommL : commV ψK.range = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨u₀, hu₀, rfl⟩ := exists_wOf hUN w
    let πU : ↥U₁ →* ↥(tildeOf Z U₁) :=
      ((secMk (Subgroup.normalizer (Z : Set G)) Z).comp (Subgroup.inclusion hUN)).codRestrict
        (tildeOf Z U₁) (fun x => secMk_mem_secImg (x := Subgroup.inclusion hUN x) x.2)
    have hπ : ∀ (u : G) (hu : u ∈ U₁), πU ⟨u, hu⟩ = wOf hUN hu := fun u hu => rfl
    set S : Subgroup G := ((commV ψK.range).comap πU).map U₁.subtype with hS
    have hZS : Z ≤ S := by
      intro z hz
      refine ⟨⟨z, hZU hz⟩, ?_, rfl⟩
      show πU ⟨z, hZU hz⟩ ∈ commV ψK.range
      rw [hπ, wOf_eq_one hUN hz]
      exact (commV ψK.range).one_mem
    have hCS : ⁅U₁, K⁆ ≤ S := by
      rw [Subgroup.commutator_le]
      intro u hu k hk
      have hc : ⁅u, k⁆ ∈ U₁ := by
        have h1 : u * (k * u⁻¹ * k⁻¹) ∈ U₁ := U₁.mul_mem hu (by
          simpa using hconjU k hk u⁻¹ (U₁.inv_mem hu))
        simpa [commutatorElement_def, mul_assoc] using h1
      refine ⟨⟨⁅u, k⁆, hc⟩, ?_, rfl⟩
      show πU ⟨⁅u, k⁆, hc⟩ ∈ commV ψK.range
      have hku : k * u * k⁻¹ ∈ U₁ := hconjU k hk u hu
      have hmem : ψK ⟨k, hk⟩ (wOf hUN hu) * (wOf hUN hu)⁻¹ ∈ commV ψK.range :=
        Subgroup.subset_closure ⟨ψK ⟨k, hk⟩, ⟨⟨k, hk⟩, rfl⟩, wOf hUN hu, rfl⟩
      have heq : πU ⟨⁅u, k⁆, hc⟩ = (ψK ⟨k, hk⟩ (wOf hUN hu) * (wOf hUN hu)⁻¹)⁻¹ := by
        rw [hπ]
        have e1 : ψK ⟨k, hk⟩ (wOf hUN hu) = wOf hUN hku := rhoN_wOf hUN (hKN hk) hu hku
        rw [e1, ← wOf_inv hUN hu, ← wOf_mul hUN hku (U₁.inv_mem hu),
          ← wOf_inv hUN (U₁.mul_mem hku (U₁.inv_mem hu))]
        exact wOf_congr hUN _ _ (by simp [commutatorElement_def, mul_assoc])
      rw [heq]
      exact (commV ψK.range).inv_mem hmem
    have hUS : U₁ ≤ S := by
      rw [← hperf]
      exact sup_le hCS hZS
    obtain ⟨y, hy, hyu⟩ := hUS hu₀
    have hyeq : y = ⟨u₀, hu₀⟩ := Subtype.ext hyu
    subst hyeq
    exact hy
  have hker : (pCoreOf 2 K).subgroupOf K ≤ ψK.ker := by
    intro k hk
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun w => ?_
    obtain ⟨u, hu, rfl⟩ := exists_wOf hUN w
    exact (rhoN_wOf_eq_iff hUN (hKN k.2) hu).mpr (hQ _ (Subgroup.mem_subgroupOf.mp hk) u hu)
  let φ : KBar K →* MulAut ↥(tildeOf Z U₁) := QuotientGroup.lift _ ψK hker
  have hφmk : ∀ k : ↥K, φ (QuotientGroup.mk k) = ψK k := fun k => rfl
  obtain ⟨e⟩ := hA
  have hsimple : IsSimpleGroup (KBar K) := by
    have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases hsimple.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      have htriv : ∀ k : ↥K, ψK k = 1 := fun k => by
        have : QuotientGroup.mk k ∈ φ.ker := by rw [h]; exact Subgroup.mem_top _
        exact this
      have hle : commV ψK.range ≤ ⊥ := by
        rw [commV, Subgroup.closure_le]
        rintro _ ⟨x, ⟨k, rfl⟩, v, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_bot, htriv k]
        exact mul_inv_cancel v
      rw [hcommL] at hle
      have hnt : Nontrivial ↥(tildeOf Z U₁) :=
        Finite.one_lt_card_iff_nontrivial.mp (by rw [hWcard]; norm_num)
      obtain ⟨w, hw⟩ : ∃ w : ↥(tildeOf Z U₁), w ≠ 1 := exists_ne 1
      exact hw (Subgroup.mem_bot.mp (hle (Subgroup.mem_top w)))
  have hrange : φ.range = ψK.range := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨QuotientGroup.mk k, rfl⟩
  have hLA6 : Nonempty (↥ψK.range ≃* ↥(alternatingGroup (Fin 6))) :=
    ⟨((MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hφinj).symm).trans e⟩
  have hP2' : IsPGroup 2 ↥ψP.range :=
    hP2.of_surjective ψP.rangeRestrict ψP.rangeRestrict_surjective
  have hnorm : ψP.range ≤ Subgroup.normalizer (ψK.range : Set (MulAut ↥(tildeOf Z U₁))) := by
    have key : ∀ a ∈ ψP.range, ∀ x ∈ ψK.range, a * x * a⁻¹ ∈ ψK.range := by
      rintro _ ⟨p, rfl⟩ _ ⟨k, rfl⟩
      have hpk : (p : G) * k * (p : G)⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hPK p.2) k).mp k.2
      refine ⟨⟨p * k * p⁻¹, hpk⟩, ?_⟩
      show rhoN Z U₁ (Subgroup.inclusion hKN ⟨p * k * p⁻¹, hpk⟩) =
        rhoN Z U₁ (Subgroup.inclusion hPN p) * rhoN Z U₁ (Subgroup.inclusion hKN k) *
          (rhoN Z U₁ (Subgroup.inclusion hPN p))⁻¹
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key a ha x hx, fun hx => ?_⟩
    have := key a⁻¹ (ψP.range.inv_mem ha) _ hx
    simpa [mul_assoc] using this
  have hnot := hI ↥(tildeOf Z U₁) hW2 hWcard ψK.range ψP.range hLA6 hcommL hP2' hnorm
  obtain ⟨w, hwP, hwL⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  obtain ⟨u, hu, rfl⟩ := exists_wOf hUN w
  refine ⟨u, hu, ?_, fun p hp => ?_⟩
  · by_contra hcon
    push Not at hcon
    refine hwL (mem_fixV.mpr ?_)
    rintro _ ⟨k, rfl⟩
    exact (rhoN_wOf_eq_iff hUN (hKN k.2) hu).mpr (hcon k k.2)
  · exact (rhoN_wOf_eq_iff hUN (hPN hp) hu).mp (mem_fixV.mp hwP (ψP ⟨p, hp⟩) ⟨⟨p, hp⟩, rfl⟩)

end Main

end Der6C

end CFSG.Quasithin
