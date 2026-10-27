module

public import CFSG.Quasithin.EmptyFaithful.S146zEPure
public import CFSG.Quasithin.EmptyFaithful.S146F23

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin.ThreeD

section Choice

variable {G : Type} [Group G] [Finite G] {T M K U₁ U₂ : Subgroup G} {s : G}

local notation "Zz" => quasithinOmegaOneCenter T

omit [Finite G] in
theorem exists_nc_of_mem_sec8 {Z U₁ K : Subgroup G} (h : Sec8 K Z U₁) {a : G} (haU : a ∈ U₁)
    (haZ : a ∉ Z) : ∃ k ∈ K, k * a * k⁻¹ * a⁻¹ ∉ Z := by
  by_contra hcon
  push Not at hcon
  have haN := h.norm haU
  have ha2 := h.sq a haU
  have hWU : twoCoset Z a haN ha2 ≤ U₁ := by
    rintro x (hx | hx)
    · exact h.le hx
    · have e : x = (x * a) * a⁻¹ := by group
      rw [e]
      exact U₁.mul_mem (h.le hx) (U₁.inv_mem haU)
  have key : ∀ k ∈ K, ∀ x ∈ twoCoset Z a haN ha2, k * x * k⁻¹ ∈ twoCoset Z a haN ha2 := by
    intro k hk x hx
    rcases hx with hx | hx
    · exact Or.inl ((Subgroup.mem_normalizer_iff.mp (h.KZ hk) x).mp hx)
    · refine Or.inr ?_
      have h1 : k * (x * a) * k⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (h.KZ hk) _).mp hx
      have hc := hcon k hk
      have h2 : a⁻¹ * (k * a * k⁻¹ * a⁻¹)⁻¹ * a ∈ Z := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) _).mp (Z.inv_mem hc)
        simpa using this
      have e : k * x * k⁻¹ * a = (k * (x * a) * k⁻¹) * (a⁻¹ * (k * a * k⁻¹ * a⁻¹)⁻¹ * a) := by
        group
      rw [e]
      exact Z.mul_mem h1 h2
  have hKW : K ≤ Subgroup.normalizer (twoCoset Z a haN ha2 : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key k hk x hx, fun hx => ?_⟩
    have h1 := key k⁻¹ (K.inv_mem hk) _ hx
    have e : k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x := by group
    rwa [e] at h1
  rcases h.irr _ (le_twoCoset haN ha2) hWU hKW with hW | hW
  · exact haZ (by
      have := mem_twoCoset_self haN ha2
      rwa [hW] at this)
  · have hd : Z.relIndex U₁ ∣ 2 := by
      rw [Subgroup.relIndex_dvd_two_iff]
      refine ⟨a, haU, fun b hb => ?_⟩
      rw [← hW] at hb
      exact hb.symm
    rw [h.card] at hd
    omega

theorem exists_fixed_vector (S : Setting146 G T M) (cK : ThreeC.CCtx T M K U₁ U₂ s) :
    ∃ u ∈ U₁, u ∉ Zz ∧ T ⊓ Subgroup.normalizer (U₁ : Set G) ≤ tZero T u := by
  classical
  set P : Subgroup G := T ⊓ Subgroup.normalizer (U₁ : Set G) with hP
  have hPZ : P ≤ Subgroup.normalizer (Zz : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (le_centralizer_quasithinOmegaOneCenter T hx.1)
  have hPU : P ≤ Subgroup.normalizer (U₁ : Set G) := inf_le_right
  have hUZ : U₁ ≤ Subgroup.normalizer (Zz : Set G) := cK.hSec.norm
  have hP2 : IsPGroup 2 ↥P := S.hyp.sylow.1.to_le inf_le_left
  let _ : MulAction ↥P ↥(tildeOf Zz U₁) := MulAction.compHom _ (secRho hPZ hPU)
  have hcard : 2 ∣ Nat.card ↥(tildeOf Zz U₁) := by rw [cK.hSec.card_tilde]; norm_num
  have hfix1 : (1 : ↥(tildeOf Zz U₁)) ∈ MulAction.fixedPoints ↥P ↥(tildeOf Zz U₁) := by
    intro x
    show (secRho hPZ hPU x) 1 = 1
    exact map_one _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb, hb1⟩ :=
    hP2.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := ↥(tildeOf Zz U₁)) hcard hfix1
  obtain ⟨x', hx', hxb⟩ := mem_secImg.mp b.2
  have hbeq : b = tildeElt hUZ (x' : G) hx' := Subtype.ext hxb.symm
  have hu2 : (x' : G) * (x' : G) = 1 := by
    have hUab : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two S.isHTM_mcOf
    have := isElemAbelian_pow_eq_one hUab (cK.hU₁U hx')
    simpa [pow_two] using this
  refine ⟨x', hx', ?_, ?_⟩
  · intro hZ
    apply hb1
    rw [hbeq]
    apply Subtype.ext
    simp only [tildeElt]
    exact (secMk_eq_one_iff.mpr hZ).symm
  · intro x hxP
    have hfx : (secRho hPZ hPU ⟨x, hxP⟩) b = b := hb ⟨x, hxP⟩
    rw [hbeq] at hfx
    have h1 := (secRho_apply_tildeElt_iff hPZ hPU hUZ ⟨x, hxP⟩ (x' : G) hx').mp hfx
    show x ∈ centralizerMod Zz T (Subgroup.zpowers (x' : G))
    rw [mem_centralizerMod_zpowers_iff hu2]
    refine ⟨hxP.1, hPZ hxP, ?_⟩
    have e : (x' : G) * x * (x' : G)⁻¹ * x⁻¹ = (x * (x' : G) * x⁻¹ * (x' : G)⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ h1

theorem exists_pctx (S : Setting146 G T M) (hB : HypB146 T M) (h5 : Stage1461Five)
    (iU1 : Input14624U1) (iU3 : Input14624U3) (iKM : Input14624KMoves)
    (c19 : Conc14619 T M) (c20 : Conc14620 T M) (c23 : Conc14623 T M)
    (hK : K ∈ cComp (mcOf T)) (c21 : Conc14621 T K) (c22 : Conc14622 T M K)
    (hL3 : KbarIsL3Two K) (hdec : IsDecompUK T M K U₁ U₂ s) (hC2 : ¬ IsCase2 T K) :
    ∃ u : G, PCtx T M K U₁ U₂ s u := by
  classical
  have cK : ThreeC.CCtx T M K U₁ U₂ s := ThreeC.CCtx.ofDecomp S c19 hK hL3 hdec
  obtain ⟨u, huU, huZ, hT⟩ := exists_fixed_vector S cK
  have hunc : ¬ ⁅Subgroup.zpowers u, K⁆ ≤ Zz := by
    intro hle
    obtain ⟨k, hk, hnc⟩ := exists_nc_of_mem_sec8 cK.hSec huU huZ
    apply hnc
    have h1 : ⁅u, k⁆ ∈ ⁅Subgroup.zpowers u, K⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers u) hk
    have h2 := Subgroup.inv_mem _ (hle h1)
    rw [commutatorElement_def] at h2
    have e : k * u * k⁻¹ * u⁻¹ = (u * k * u⁻¹ * k⁻¹)⁻¹ := by group
    rw [e]; exact h2
  have hch : IsChoiceU T M K U₁ u := Or.inl ⟨hC2, huU, hunc, hT⟩
  have hctx : Ctx24 T M K U₁ U₂ s u := ⟨c19, c20, c23, hK, c21, c22, hdec, hch⟩
  have hinv : IsInvU T M (mcOf T) u :=
    isInvU24_of_parts hK hdec hch (iU1 G T M S hB K U₁ U₂ s u hctx)
      (iU3 G T M S hB K U₁ U₂ s u hctx)
      (input14624U2_of_moves h5 iKM G T M S hB K U₁ U₂ s u hctx)
  exact ⟨u, { toCCtx := cK, huU := huU, huZ := huZ, hinv := hinv }⟩

end Choice

end CFSG.Quasithin.ThreeD
