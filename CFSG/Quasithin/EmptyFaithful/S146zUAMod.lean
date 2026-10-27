module

public import CFSG.Quasithin.EmptyFaithful.S146zHFix
public import CFSG.Quasithin.EmptyFaithful.S146zRImg
public import CFSG.Quasithin.EmptyFaithful.S146zUAPair
public import CFSG.Quasithin.EmptyFaithful.SBc16SAut

public section

namespace CFSG.Quasithin.S146zU.UA

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
  CFSG.Quasithin.C1Pack
open scoped commutatorElement

section Rho

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}
  (hG : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) (mcOf T))

theorem hypG (S : Setting146 G T M) :
    HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) (mcOf T) :=
  (S.lemma_14_5_14 (S.isHz_iff.mpr S.isHTM_mcOf)).2.toHypF91

@[expose] noncomputable def rhoBar : OTwoQuot (mcOf T) →* MulAut (UMod hG) :=
  QuotientGroup.lift (CFSG.Open.pCore 2 ↥(mcOf T)) (rhoH hG) (fun g hg => by
    rw [MonoidHom.mem_ker, rhoH_eq_one_iff hG g]
    exact ⟨g, hg, rfl⟩)

theorem rhoBar_qPi (g : ↥(mcOf T)) : rhoBar hG (qPi (mcOf T) g) = rhoH hG g := rfl

theorem rhoBar_injective : Function.Injective (rhoBar hG) := by
  rw [injective_iff_map_eq_one]
  intro n hn
  obtain ⟨g, rfl⟩ := qPi_surjective (mcOf T) n
  rw [rhoBar_qPi, rhoH_eq_one_iff] at hn
  obtain ⟨g', hg', hg'g⟩ := hn
  have : g' = g := Subtype.ext hg'g
  subst this
  exact (QuotientGroup.eq_one_iff _).mpr hg'

@[expose] noncomputable def Lof (K : Subgroup G) : Subgroup (MulAut (UMod hG)) :=
  (imageOTwoQuot (mcOf T) K).map (rhoBar hG)

theorem mem_Lof {K : Subgroup G} {g : MulAut (UMod hG)} :
    g ∈ Lof hG K ↔ ∃ k : ↥(mcOf T), (k : G) ∈ K ∧ rhoH hG k = g := by
  constructor
  · rintro ⟨n, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, Subgroup.mem_subgroupOf.mp hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨qPi (mcOf T) k, ⟨k, Subgroup.mem_subgroupOf.mpr hk, rfl⟩, rfl⟩

end Rho

section Wsub

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}
  (hG : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) (mcOf T))

theorem Wsub_le_fixV_iff {J K : Subgroup G} (hJU : J ≤ conjClosure (VZ T M) (mcOf T))
    (hKG : K ≤ mcOf T) :
    Wsub hG J ≤ fixV (Lof hG K) ↔ ⁅J, K⁆ ≤ quasithinOmegaOneCenter T := by
  constructor
  · intro h
    rw [Subgroup.commutator_le]
    intro u hu k hk
    have hu' : u ∈ conjClosure (VZ T M) (mcOf T) := hJU hu
    have hw : clsU hG hu' ∈ Wsub hG J := clsU_mem_Wsub hG hu' hu
    have hfix := h hw (rhoH hG ⟨k, hKG hk⟩) ((mem_Lof hG).mpr ⟨⟨k, hKG hk⟩, hk, rfl⟩)
    have h1 : k * u * k⁻¹ * u⁻¹ ∈ quasithinOmegaOneCenter T :=
      (rhoH_clsU_eq_iff hG ⟨k, hKG hk⟩ hu').mp hfix
    have e : ⁅u, k⁆ = (k * u * k⁻¹ * u⁻¹)⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    exact (quasithinOmegaOneCenter T).inv_mem h1
  · intro h w hw g hg
    obtain ⟨u, hu', huJ, rfl⟩ := exists_clsU_of_mem_Wsub hG hJU hw
    obtain ⟨⟨k, hkG⟩, hk, rfl⟩ := (mem_Lof hG).mp hg
    refine (rhoH_clsU_eq_iff hG ⟨k, hkG⟩ hu').mpr ?_
    have h1 : ⁅u, k⁆ ∈ quasithinOmegaOneCenter T :=
      h (Subgroup.commutator_mem_commutator huJ hk)
    have e : k * u * k⁻¹ * u⁻¹ = (⁅u, k⁆)⁻¹ := by rw [commutatorElement_def]; group
    show k * u * k⁻¹ * u⁻¹ ∈ quasithinOmegaOneCenter T
    rw [e]
    exact (quasithinOmegaOneCenter T).inv_mem h1

theorem commV_Lof_le_Wsub {K : Subgroup G} (hKG : K ≤ mcOf T) :
    commV (Lof hG K) ≤ Wsub hG ⁅conjClosure (VZ T M) (mcOf T), K⁆ := by
  have hU : ⁅conjClosure (VZ T M) (mcOf T), K⁆ ≤ conjClosure (VZ T M) (mcOf T) :=
    S145.commutator_le_of_le_normalizer (hKG.trans (le_normalizer_conjClosure _ _))
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨g, hg, v, rfl⟩
  obtain ⟨⟨k, hkG⟩, hk, rfl⟩ := (mem_Lof hG).mp hg
  obtain ⟨u, hu, rfl⟩ := exists_clsU hG v
  have hcomm : k * u * k⁻¹ * u⁻¹ ∈ ⁅conjClosure (VZ T M) (mcOf T), K⁆ := by
    have e : k * u * k⁻¹ * u⁻¹ = (⁅u, k⁆)⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hu hk)
  have e : rhoH hG ⟨k, hkG⟩ (clsU hG hu) * (clsU hG hu)⁻¹ = clsU hG (hU hcomm) := by
    rw [rhoH_clsU, clsU_inv, clsU_mul]
  rw [SetLike.mem_coe, e]
  exact clsU_mem_Wsub hG (hU hcomm) hcomm

theorem commV_Lof_le_fixV {K₁ K₂ : Subgroup G} (hK₁ : K₁ ≤ mcOf T) (hK₂ : K₂ ≤ mcOf T)
    (hD : ⁅⁅conjClosure (VZ T M) (mcOf T), K₁⁆, K₂⁆ ≤ quasithinOmegaOneCenter T) :
    commV (Lof hG K₁) ≤ fixV (Lof hG K₂) :=
  (commV_Lof_le_Wsub hG hK₁).trans
    ((Wsub_le_fixV_iff hG (S145.commutator_le_of_le_normalizer
      (hK₁.trans (le_normalizer_conjClosure _ _))) hK₂).mpr hD)

end Wsub

section Fix

variable {G : Type} [Group G] [Finite G] {T M H PQ H₀ H₁ H₂ : Subgroup G} {p : ℕ} {t : G}
  (hG : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) (mcOf T))

theorem eq_one_of_fix' (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) (φ : ↥H₁ →* DihedralGroup p)
    (hker : ∀ y : ↥H₁, φ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) {a : ↥H₁}
    (ha : φ a = DihedralGroup.r 1) (haG : (a : G) ∈ mcOf T) {w : UMod hG}
    (hw : w ∈ Wsub hG (uHi T M H H₁)) (hfix : rhoH hG ⟨a, haG⟩ w = w) : w = 1 := by
  have hH : IsHz T M (yOfL22 T M) H := S.isHz_iff.mpr hred.isHTM
  have h91H := (S.lemma_14_5_14 hH).2.toHypF91
  have hHG : H ≤ mcOf T := S.le_mcOf hred.isHTM
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hU1 : uHi T M H H₁ ≤ conjClosure (VZ T M) (mcOf T) :=
    (uHi_le_conjClosure hH₁H).trans (conjClosure_mono le_rfl hHG)
  obtain ⟨u, hu, huJ, rfl⟩ := exists_clsU_of_mem_Wsub hG hU1 hw
  have hu₂ : u ∈ conjClosure (VZ T M) H := uHi_le_conjClosure hH₁H huJ
  have haH : (a : G) ∈ H := h.le (h.le₁ a.2)
  have hw₂ : clsU h91H hu₂ ∈ Wsub h91H (uHi T M H H₁) := clsU_mem_Wsub h91H hu₂ huJ
  have hfix₂ : rhoH h91H ⟨a, haH⟩ (clsU h91H hu₂) = clsU h91H hu₂ := by
    rw [rhoH_clsU_eq_iff]
    exact (rhoH_clsU_eq_iff hG ⟨a, haG⟩ hu).mp hfix
  have h1 := IsDecP.eq_one_of_fix S hred h h91H φ hker ha hw₂ hfix₂
  rw [clsU_eq_one_iff] at h1
  exact (clsU_eq_one_iff hG hu).mpr h1

theorem exists_eq_mul_inv (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) (φ : ↥H₁ →* DihedralGroup p)
    (hker : ∀ y : ↥H₁, φ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) {a : ↥H₁}
    (ha : φ a = DihedralGroup.r 1) (haG : (a : G) ∈ mcOf T) :
    ∀ w ∈ Wsub hG (uHi T M H H₁), ∃ u ∈ Wsub hG (uHi T M H H₁),
      w = rhoH hG ⟨a, haG⟩ u * u⁻¹ := by
  classical
  have hHG : H ≤ mcOf T := S.le_mcOf hred.isHTM
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hU1 : uHi T M H H₁ ≤ conjClosure (VZ T M) (mcOf T) :=
    (uHi_le_conjClosure hH₁H).trans (conjClosure_mono le_rfl hHG)
  set X₁ := Wsub hG (uHi T M H H₁) with hX₁
  have hmem : ∀ u ∈ X₁, rhoH hG ⟨a, haG⟩ u * u⁻¹ ∈ X₁ := by
    intro u hu
    refine X₁.mul_mem ?_ (X₁.inv_mem hu)
    exact rhoH_mem_Wsub hG ⟨a, haG⟩ hU1
      (F7.conjSub_eq_of_mem_normalizer (h.le_normalizer_uHi S hred a.2)) hu
  have hinj : Function.Injective (fun u : X₁ =>
      (⟨rhoH hG ⟨a, haG⟩ u * (u : UMod hG)⁻¹, hmem u u.2⟩ : X₁)) := by
    intro u v huv
    have h1 : rhoH hG ⟨a, haG⟩ u * (u : UMod hG)⁻¹ = rhoH hG ⟨a, haG⟩ v * (v : UMod hG)⁻¹ :=
      congrArg Subtype.val huv
    have h1' : rhoH hG ⟨a, haG⟩ u / (u : UMod hG) = rhoH hG ⟨a, haG⟩ v / (v : UMod hG) := by
      simpa only [div_eq_mul_inv] using h1
    have h2 : rhoH hG ⟨a, haG⟩ ((u : UMod hG) * (v : UMod hG)⁻¹) =
        (u : UMod hG) * (v : UMod hG)⁻¹ := by
      rw [map_mul, map_inv]
      simpa only [div_eq_mul_inv] using div_eq_div_iff_div_eq_div.mp h1'
    have h3 : (u : UMod hG) * (v : UMod hG)⁻¹ = 1 :=
      eq_one_of_fix' hG S hred h φ hker ha haG (X₁.mul_mem u.2 (X₁.inv_mem v.2)) h2
    exact Subtype.ext (mul_inv_eq_one.mp h3)
  have hsurj := Finite.injective_iff_surjective.mp hinj
  intro w hw
  obtain ⟨u, hu⟩ := hsurj ⟨w, hw⟩
  exact ⟨u, u.2, (congrArg Subtype.val hu).symm⟩

theorem Wsub_ne_bot (S : Setting146 G T M) (hred : IsRedCE T M H PQ 5)
    (h : IsDecP T M H 5 H₀ H₁ H₂ t) : Wsub hG (uHi T M H H₁) ≠ ⊥ := by
  have h4 : mIdx (uHi T M H H₁) (quasithinOmegaOneCenter T) = 4 := h.rank₁.1 rfl
  have hne : uHi T M H H₁ ≠ quasithinOmegaOneCenter T := by
    intro heq
    rw [heq] at h4
    simp [mIdx] at h4
  obtain ⟨u, huJ, huZ⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne (Z_le_uHi T M H H₁) hne.symm)
  have hHG : H ≤ mcOf T := S.le_mcOf hred.isHTM
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hU1 : uHi T M H H₁ ≤ conjClosure (VZ T M) (mcOf T) :=
    (uHi_le_conjClosure hH₁H).trans (conjClosure_mono le_rfl hHG)
  have hu' : u ∈ conjClosure (VZ T M) (mcOf T) := hU1 huJ
  intro hbot
  have hw : clsU hG hu' ∈ Wsub hG (uHi T M H H₁) := clsU_mem_Wsub hG hu' huJ
  rw [hbot, Subgroup.mem_bot, clsU_eq_one_iff] at hw
  exact huZ hw

end Fix

section Card

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}
  (hG : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) (mcOf T))

theorem card_image_eq {G₁ K : Subgroup G} (hK : K ∈ cComp G₁)
    (e : Nonempty (OTwoQuot K ≃* SBc16.L216)) :
    Nat.card ↥(imageOTwoQuot G₁ K) = 4080 ∧ IsSimpleGroup ↥(imageOTwoQuot G₁ K) := by
  obtain ⟨e₁⟩ := e
  obtain ⟨e₂⟩ := q_oTwoQuot_equiv_image (subnormal_of_mem_cComp hK)
  have e₃ : ↥(imageOTwoQuot G₁ K) ≃* SBc16.L216 := e₂.symm.trans e₁
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr e₃.toEquiv]
    exact SBc16.card_L216
  · have := SBc16.isSimpleGroup_L216
    exact e₃.isSimpleGroup

theorem Lof_h5 {K : Subgroup G} (hcard : Nat.card ↥(imageOTwoQuot (mcOf T) K) = 4080) :
    ∀ c ∈ Lof hG K, ∀ d ∈ Lof hG K, c ^ 5 = 1 → d ^ 5 = 1 → c * d = d * c → c ≠ 1 →
      d ∈ Subgroup.zpowers c := by
  intro c hc d hd hc5 hd5 hcd hc1
  have hdvd : Nat.card ↥(Lof hG K) ∣ 4080 := hcard ▸ Subgroup.card_map_dvd _ _
  have h25 : ¬ 5 ^ 2 ∣ Nat.card ↥(Lof hG K) := fun h => by
    have := h.trans hdvd
    norm_num at this
  have key := mem_zpowers_of_not_dvd_sq (Γ := ↥(Lof hG K)) Nat.prime_five h25
    (c := ⟨c, hc⟩) (d := ⟨d, hd⟩) (Subtype.ext (by simpa using hc5))
    (Subtype.ext (by simpa using hd5)) (Subtype.ext hcd)
    (fun h => hc1 (congrArg Subtype.val h))
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp key
  exact Subgroup.mem_zpowers_iff.mpr ⟨m, by simpa using congrArg Subtype.val hm⟩

end Card

end CFSG.Quasithin.S146zU.UA
