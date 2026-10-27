module

public import CFSG.Quasithin.EmptyFaithful.A38c16Sec
public import CFSG.Quasithin.Background.S1549DBr
public import CFSG.Quasithin.Background.S1549DGen

public section

namespace CFSG.Quasithin.A38c16

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement MatrixGroups

section Concrete

open CFSG.Quasithin.S1549C CFSG.Quasithin.S1549D

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}

@[expose] noncomputable def vecHom (h : HypF91 T V L V₁ Vp H) :
    ↥(conjClosure Vp H) →* ↥(tildeOf V₁ (conjClosure Vp H)) :=
  ((secMk (Subgroup.normalizer (V₁ : Set G)) V₁).comp
      (Subgroup.inclusion (fun _ hu => mem_normalizer_of_mem_conjClosure h hu))).codRestrict _
    (fun u => secMk_mem_secImg (x := Subgroup.inclusion
      (fun _ hu => mem_normalizer_of_mem_conjClosure h hu) u) u.2)

theorem vecHom_apply (h : HypF91 T V L V₁ Vp H) (a : G) (ha : a ∈ conjClosure Vp H) :
    vecHom h ⟨a, ha⟩ = vecOf h a ha := rfl

theorem secData (h : HypF91 T V L V₁ Vp H) :
    @SecData G _ ↥(tildeOf V₁ (conjClosure Vp H)) (modInst h) H (conjClosure Vp H) V₁ (vecHom h)
      (starHom h) := by
  let _ : CommGroup ↥(tildeOf V₁ (conjClosure Vp H)) := modInst h
  refine
    { norm := fun x hx u hu =>
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure Vp H hx) u).mp hu
      Z_le := h.V₁_le_Vp.trans (le_conjClosure Vp H)
      surj := fun w => ?_
      ker := fun u => ?_
      act := fun x u => ?_ }
  · obtain ⟨x, hx, hxw⟩ := mem_secImg.mp w.2
    exact ⟨⟨(x : G), hx⟩, Subtype.ext hxw⟩
  · have := vecOf_eq_one_iff h u.2
    rw [← vecHom_apply h u u.2] at this
    exact this
  · have := starHom_vecOf h x u.2
    rw [← vecHom_apply h u u.2] at this
    exact this

end Concrete


section Cent

open CFSG.ComponentClassification CFSG.QuasithinUnique.Setup.Family

theorem sl3_central_eq_one (c : SL(3, ZMod 2)) (hc : ∀ s : SL(3, ZMod 2), c * s = s * c) : c = 1 := by
  have h1 : (slEquivGL 3 c) ∈ Subgroup.center GL32 := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨s, rfl⟩ := (slEquivGL 3).surjective g
    rw [← map_mul, ← map_mul, hc s]
  rw [center_GL32, Subgroup.mem_bot] at h1
  exact (slEquivGL 3).injective (h1.trans (map_one _).symm)

variable {Gm : Type} [Group Gm]

theorem central_eq_one_of_equiv {L : Subgroup Gm} (θ : ↥L ≃* SL(3, ZMod 2)) :
    ∀ x ∈ L, (∀ y ∈ L, x * y = y * x) → x = 1 := by
  intro x hx hxc
  have h1 : θ ⟨x, hx⟩ = 1 := by
    refine sl3_central_eq_one _ fun s => ?_
    obtain ⟨y, rfl⟩ := θ.surjective s
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hxc y y.2)
  have := θ.injective (h1.trans (map_one θ).symm)
  exact congrArg Subtype.val this

theorem mem_sup_of_comm {L₁ L₂ : Subgroup Gm} (hcomm : ∀ k ∈ L₁, ∀ y ∈ L₂, k * y = y * k)
    {x : Gm} (hx : x ∈ L₁ ⊔ L₂) : ∃ k ∈ L₁, ∃ y ∈ L₂, x = k * y := by
  let P : Subgroup Gm :=
    { carrier := {x | ∃ k ∈ L₁, ∃ y ∈ L₂, x = k * y}
      mul_mem' := by
        rintro _ _ ⟨k₁, hk₁, y₁, hy₁, rfl⟩ ⟨k₂, hk₂, y₂, hy₂, rfl⟩
        refine ⟨k₁ * k₂, L₁.mul_mem hk₁ hk₂, y₁ * y₂, L₂.mul_mem hy₁ hy₂, ?_⟩
        have : y₁ * k₂ = k₂ * y₁ := (hcomm k₂ hk₂ y₁ hy₁).symm
        calc k₁ * y₁ * (k₂ * y₂) = k₁ * (y₁ * k₂) * y₂ := by group
          _ = k₁ * (k₂ * y₁) * y₂ := by rw [this]
          _ = k₁ * k₂ * (y₁ * y₂) := by group
      one_mem' := ⟨1, L₁.one_mem, 1, L₂.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨k, hk, y, hy, rfl⟩
        refine ⟨k⁻¹, L₁.inv_mem hk, y⁻¹, L₂.inv_mem hy, ?_⟩
        rw [mul_inv_rev]
        exact (hcomm k⁻¹ (L₁.inv_mem hk) y⁻¹ (L₂.inv_mem hy)).symm }
  have hle : L₁ ⊔ L₂ ≤ P := sup_le (fun k hk => ⟨k, hk, 1, L₂.one_mem, by simp⟩)
    (fun y hy => ⟨1, L₁.one_mem, y, hy, by simp⟩)
  exact hle hx

theorem case3_cent [Finite Gm] {Γ L₁ L₂ T₀ : Subgroup Gm} (hL₁ : L₁ ≤ Γ) (hL₂ : L₂ ≤ Γ)
    (hn₁ : ∀ g ∈ Γ, ∀ k ∈ L₁, g * k * g⁻¹ ∈ L₁) (hn₂ : ∀ g ∈ Γ, ∀ k ∈ L₂, g * k * g⁻¹ ∈ L₂)
    (hcomm : ∀ k ∈ L₁, ∀ y ∈ L₂, k * y = y * k)
    (hZ₁ : ∀ x ∈ L₁, (∀ y ∈ L₁, x * y = y * x) → x = 1)
    (hZ₂ : ∀ x ∈ L₂, (∀ y ∈ L₂, x * y = y * x) → x = 1)
    (hT₀Γ : T₀ ≤ Γ) (hT₀ : IsPGroup 2 T₀) (hΓ : Γ = (L₁ ⊔ L₂) ⊔ T₀) (hO2 : pCoreOf 2 Γ = ⊥) :
    ∀ γ ∈ Γ, (∀ k ∈ L₁, γ * k = k * γ) → (∀ y ∈ L₂, γ * y = y * γ) → γ = 1 := by
  have hLΓ : L₁ ⊔ L₂ ≤ Γ := sup_le hL₁ hL₂
  have hnorm : ((L₁ ⊔ L₂).subgroupOf Γ).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk, y, hy, hky⟩ := mem_sup_of_comm hcomm hn
    have e : ((g * n * g⁻¹ : ↥Γ) : Gm) = ((g : Gm) * k * (g : Gm)⁻¹) * ((g : Gm) * y * (g : Gm)⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hky]
      group
    rw [e]
    exact Subgroup.mul_mem_sup (hn₁ g g.2 k hk) (hn₂ g g.2 y hy)
  have hZ : ∀ x ∈ L₁ ⊔ L₂, (∀ y ∈ L₁ ⊔ L₂, x * y = y * x) → x = 1 := by
    intro x hx hxc
    obtain ⟨k, hk, y, hy, rfl⟩ := mem_sup_of_comm hcomm hx
    have hk1 : k = 1 := by
      refine hZ₁ k hk fun k' hk' => ?_
      have h1 := hxc k' (Subgroup.mem_sup_left hk')
      have h2 : y * k' = k' * y := (hcomm k' hk' y hy).symm
      have h3 : k * k' * y = k' * k * y := by
        calc k * k' * y = k * (k' * y) := by group
          _ = k * (y * k') := by rw [h2]
          _ = k * y * k' := by group
          _ = k' * (k * y) := h1
          _ = k' * k * y := by group
      exact mul_right_cancel h3
    have hy1 : y = 1 := by
      refine hZ₂ y hy fun y' hy' => ?_
      have h1 := hxc y' (Subgroup.mem_sup_right hy')
      have h2 : y' * k = k * y' := (hcomm k hk y' hy').symm
      have h3 : k * (y * y') = k * (y' * y) := by
        calc k * (y * y') = k * y * y' := by group
          _ = y' * (k * y) := h1
          _ = (y' * k) * y := by group
          _ = (k * y') * y := by rw [h2]
          _ = k * (y' * y) := by group
      exact mul_left_cancel h3
    rw [hk1, hy1, one_mul]
  have hbot := LRed5.centralizer_eq_bot_of_two_quotient hLΓ hnorm hZ hT₀Γ hT₀ hΓ hO2
  intro γ hγ hk hy
  have hγc : γ ∈ Γ ⊓ Subgroup.centralizer ((L₁ ⊔ L₂ : Subgroup Gm) : Set Gm) := by
    refine ⟨hγ, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
    obtain ⟨k, hk', y, hy', rfl⟩ := mem_sup_of_comm hcomm hx
    calc k * y * γ = k * (y * γ) := by group
      _ = k * (γ * y) := by rw [hy y hy']
      _ = (k * γ) * y := by group
      _ = (γ * k) * y := by rw [hk k hk']
      _ = γ * (k * y) := by group
  rw [hbot, Subgroup.mem_bot] at hγc
  exact hγc

end Cent


section Interface

open CFSG.Quasithin.S1549C CFSG.Quasithin.S1549D

variable {G : Type} [Group G] [Finite G]

theorem case3_interface
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    {T M : Subgroup G} (S : Setting146 G T M) (hB : HypB146 T M)
    (c19 : Conc14619 T M) (c20 : Conc14620 T M)
    {K : Subgroup G} (hK : K ∈ cComp (mcOf T)) {Kp : Subgroup G} (hKp : Kp ∈ cComp (mcOf T))
    (hne : Kp ≠ K) (hnK : mcOf T ≤ Subgroup.normalizer (K : Set G))
    (hnKp : mcOf T ≤ Subgroup.normalizer (Kp : Set G))
    (hper : perfectCore (mcOf T) = K ⊔ Kp) (hL32 : KbarIsL3Two K) (hL32p : KbarIsL3Two Kp)
    (hsumK : ⁅uOfL22 T M, K⁆ ⊔ quasithinOmegaOneCenter T ≤
      ⨆ (J : Subgroup G) (_ : quasithinOmegaOneCenter T ≤ J ∧ J ≤ uOfL22 T M ∧
          mIdx J (quasithinOmegaOneCenter T) = 3 ∧
          IsIrredOnSection K J (quasithinOmegaOneCenter T)), J)
    (hsumKp : ⁅uOfL22 T M, Kp⁆ ⊔ quasithinOmegaOneCenter T ≤
      ⨆ (J : Subgroup G) (_ : quasithinOmegaOneCenter T ≤ J ∧ J ≤ uOfL22 T M ∧
          mIdx J (quasithinOmegaOneCenter T) = 3 ∧
          IsIrredOnSection Kp J (quasithinOmegaOneCenter T)), J) :
    ∃ (W : Type) (_ : CommGroup W) (_ : Finite W) (_ : ∀ w : W, w ^ 2 = 1)
      (Γ K' Kp' : Subgroup (MulAut W)) (_ : ↥K' ≃* SL(3, ZMod 2)) (_ : ↥Kp' ≃* SL(3, ZMod 2))
      (s : MulAut W) (A : Subgroup (MulAut W)),
      Case3Setting Γ K' Kp' ∧ s ∈ Γ ∧ IsOuterOn K' s ∧
      commSub ⊤ K' ≤ ⨆ (M : Subgroup W) (_ : IsSimple8 K' M), M ∧
      commSub ⊤ Kp' ≤ ⨆ (M : Subgroup W) (_ : IsSimple8 Kp' M), M ∧
      A ≤ Γ ∧ A ≠ ⊥ ∧ IsElemAbelian2 A ∧ Nat.card W ≤ Nat.card A ^ 2 * Nat.card (fixV A) ∧
      (commSub ⊤ K' ⊓ commSub ⊤ Kp' = ⊥ →
        (⁅uOfL22 T M, K⁆ ⊔ quasithinOmegaOneCenter T) ⊓ (⁅uOfL22 T M, Kp⁆ ⊔ quasithinOmegaOneCenter T)
          ≤ quasithinOmegaOneCenter T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHTM : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hHTM.1.1
  have hKH : K ≤ mcOf T := le_of_mem_cComp hK
  have hKpH : Kp ≤ mcOf T := le_of_mem_cComp hKp
  have hF98 := (S.lemma_14_5_14 (S.isHz_iff.mpr hHTM)).2
  have h := hF98.toHypF91
  have hc21 : ∀ K ∈ cComp (mcOf T), Conc14621 T K :=
    stage14621_of_a3 h37 h38 h39 G T M S hB c19 c20
  obtain ⟨-, hHT⟩ := conc14623_one_of_a3 h37 h38 S hB c19 c20 hc21
  have hker := starHom_eq_one_iff h
  have hWexp : ∀ w : ↥(tildeOf (quasithinOmegaOneCenter T) (conjClosure (VZ T M) (mcOf T))),
      w ^ 2 = 1 := fun w => Subtype.ext (by simpa using h.isElemAbelian_tilde.2 w w.2)
  let _ : CommGroup ↥(tildeOf (quasithinOmegaOneCenter T) (conjClosure (VZ T M) (mcOf T))) :=
    modInst h
  obtain ⟨e1⟩ := LRed5.kbar_equiv_image hK (starHom h) hker
  have hL32c := hL32
  obtain ⟨e2⟩ := hL32
  obtain ⟨e1p⟩ := LRed5.kbar_equiv_image hKp (starHom h) hker
  obtain ⟨e2p⟩ := hL32p
  let θ : ↥(starOfSub h K) ≃* SL(3, ZMod 2) := e1.symm.trans e2
  let θp : ↥(starOfSub h Kp) ≃* SL(3, ZMod 2) := e1p.symm.trans e2p
  obtain ⟨-, s, hs, hdyn⟩ := c20 _ hHTM K hK
  have hsT : s ∈ T := hs.1
  have hsK : s ∈ Subgroup.normalizer (K : Set G) := hs.2
  have hout : KbarInducesOuter K s := by
    rcases hdyn with ⟨-, hout⟩ | ⟨hA6, -⟩
    · exact hout
    · exact (not_kbarIsA6_of_kbarIsL3Two hL32c hA6).elim
  have hsH : s ∈ mcOf T := hTH hsT
  have hUp : IsPGroup 2 ↥(conjClosure (VZ T M) (mcOf T)) :=
    (pCoreOf_isPGroup 2 (mcOf T)).to_le h.conjClosure_Vp_le_pCoreOf
  have hd := secData h
  have hT2 : IsPGroup 2 T := h.sylow_H.2.1
  have hnormK : ∀ g ∈ starOfSub h (mcOf T), ∀ k ∈ starOfSub h K, g * k * g⁻¹ ∈ starOfSub h K := by
    intro g hg k hk
    obtain ⟨x, -, rfl⟩ := (mem_starOfSub h).mp hg
    exact star_norm (fun x hx k hk => (Subgroup.mem_normalizer_iff.mp (hnK hx) k).mp hk) x k hk
  have hnormKp : ∀ g ∈ starOfSub h (mcOf T), ∀ k ∈ starOfSub h Kp, g * k * g⁻¹ ∈ starOfSub h Kp := by
    intro g hg k hk
    obtain ⟨x, -, rfl⟩ := (mem_starOfSub h).mp hg
    exact star_norm (fun x hx k hk => (Subgroup.mem_normalizer_iff.mp (hnKp hx) k).mp hk) x k hk
  have hcomm : ∀ k ∈ starOfSub h K, ∀ y ∈ starOfSub h Kp, k * y = y * k :=
    star_comm hker (fun k hk y hy =>
      comm_mem_pCoreOf_of_cComp (c19 _ hHTM).1 hK hKp hne hnK hnKp hk hy)
  have hΓ : starOfSub h (mcOf T) = (starOfSub h K ⊔ starOfSub h Kp) ⊔ starOfSub h T := by
    have e1 : mcOf T = (K ⊔ Kp) ⊔ T := by rw [← hper]; exact hHT
    rw [congrArg (starOfSub h) e1, starOfSub_sup h (sup_le hKH hKpH) hTH,
      starOfSub_sup h hKH hKpH]
  have hcent := case3_cent (starOfSub_mono h hKH) (starOfSub_mono h hKpH) hnormK hnormKp hcomm
    (central_eq_one_of_equiv θ) (central_eq_one_of_equiv θp) (starOfSub_mono h hTH)
    (isPGroup_starOfSub h hTH hT2) hΓ (pCoreOf_starOfSub_H h)
  have hcs : Case3Setting (starOfSub h (mcOf T)) (starOfSub h K) (starOfSub h Kp) :=
    ⟨starOfSub_mono h hKH, starOfSub_mono h hKpH, hnormK, hnormKp, hcomm, hcent⟩
  have houter : IsOuterOn (starOfSub h K) (starHom h ⟨s, hsH⟩) :=
    LRed5.outer_transfer hK (starHom h) hker (s := ⟨s, hsH⟩) hsK hout
  obtain ⟨-, B, -, hmem⟩ := hF98.F916_3
  obtain ⟨⟨hA2, hr⟩, -⟩ := hmem
  have hGam : autOn (tildeOf (quasithinOmegaOneCenter T) (mcOf T))
      (tildeOf (quasithinOmegaOneCenter T) (conjClosure (VZ T M) (mcOf T))) =
      starOfSub h (mcOf T) := autOn_tilde_eq_map_starHom h le_rfl
  refine ⟨↥(tildeOf (quasithinOmegaOneCenter T) (conjClosure (VZ T M) (mcOf T))), modInst h,
    inferInstance, hWexp, starOfSub h (mcOf T), starOfSub h K, starOfSub h Kp, θ, θp,
    starHom h ⟨s, hsH⟩, autOn (tildeOf (quasithinOmegaOneCenter T) B)
      (tildeOf (quasithinOmegaOneCenter T) (conjClosure (VZ T M) (mcOf T))), hcs,
    (mem_starOfSub h).mpr ⟨⟨s, hsH⟩, hsH, rfl⟩, houter,
    commSub_le_iSup_simple8 hd hKH hUp hsumK, commSub_le_iSup_simple8 hd hKpH hUp hsumKp,
    ?_, hA2.2.1, hA2.2.2, (rAV_le_two_iff hWexp hA2).1 hr,
    fun hbot => inf_le_of_commSub_inf_eq_bot hd hKH hKpH hbot⟩
  rw [← hGam]
  exact hA2.1

end Interface


end CFSG.Quasithin.A38c16
