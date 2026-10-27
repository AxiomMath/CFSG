module

public import CFSG.Quasithin.Vol2.Ch3Sec1L319SevenBlk
public import CFSG.Quasithin.Vol2.Ch3wJ
public import CFSG.Quasithin.Vol2.Ch3Sec1L319Form

public section

namespace CFSG.Quasithin.H13.L319

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Ch3z RegularWreathProduct

@[expose] def Lemma319NoS5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
    ∀ M M₀ H V : Subgroup G, InM T M → ∀ h : Hyp315Base T M M₀ H V, Hyp315.CaseII M H V →
      qInt M₀ V h.reduced.2.2.1 = 2 → IsUniqueM M₀ M → V ≤ pCoreOf 2 H → ¬ IsDualFFOn M₀ V →
      Concl319 T M V H False → Six6i T M V → Six6iiiImg T M V → NoThreeInCV M V →
      NoS5Shape V H

section Aux

variable {G : Type} [Group G]

theorem IsMinOffender.le_centralizer [Finite G] {T M M₀ H V A : Subgroup G}
    (hT : quasithinIsSylowTwo T) (h : Hyp319 T M M₀ H V) (hA : IsMinOffender T H V A) :
    A ≤ Subgroup.centralizer (V : Set G) := by
  have hD := h.d11Hyp hT
  have hnff : ¬ IsFFInt M₀ V h.reduced.2.2.1 := fun hff =>
    h.not_qInt_le_one ((isFFInt_iff_qInt_le_one _ _ _).mp hff)
  exact (B6.le_thompsonJ hA.1).trans
    ((hD.thompsonJ_le hnff).trans (hD.centralizer.le.trans inf_le_right))

theorem conj_mem_centralizer {V : Subgroup G} {g d : G} (hg : g ∈ Subgroup.normalizer (V : Set G))
    (hd : d ∈ Subgroup.centralizer (V : Set G)) : g * d * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hd ⊢
  intro v hv
  have hv' : g⁻¹ * v * g ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) v).mp hv
    simpa using this
  have h1 := hd _ hv'
  calc v * (g * d * g⁻¹) = g * ((g⁻¹ * v * g) * d) * g⁻¹ := by group
    _ = g * (d * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
    _ = (g * d * g⁻¹) * v := by group

end Aux

section Chief

variable {G : Type} [Group G] [Finite G] {H T M₂ U A L N : Subgroup G}

theorem chiefImg_mono' (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) {K K' : Subgroup G} (h : K ≤ K') :
    chiefImg hHL hHN K ≤ chiefImg hHL hHN K' := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  exact Subgroup.mem_map.mpr ⟨y, Subgroup.mem_subgroupOf.mpr (h (Subgroup.mem_subgroupOf.mp hy)), rfl⟩

theorem exists_psi_orderOf_five {Y : Type*} [Group Y] (h : Setting H T M₂ U A)
    (hstep : IsChiefStep H U L N) (φ : ↥H →* Y) (hφs : Function.Surjective φ)
    (hφk : φ.ker = (cSecIn H L N).subgroupOf H) {y : Y} (hy : orderOf y = 5) :
    ∃ g : ↥H, orderOf (chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) g) = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hHL := Setting.hHL hstep
  have hHN := Setting.hHN hstep
  have hNL := h.hNL hstep
  obtain ⟨g, hg⟩ := hφs y
  have hker : ∀ g' : ↥H, chiefPsi hHL hHN g' = 1 ↔ φ g' = 1 := by
    intro g'
    have e1 : chiefPsi hHL hHN g' = 1 ↔ chiefHom hHL hHN g' = 1 :=
      ⟨fun hh => Subtype.ext hh, fun hh => congrArg Subtype.val hh⟩
    rw [e1, chiefHom_eq_one_iff hHL hHN hNL g', ← cSecIn_eq_centralizerMod le_rfl hstep.2.1,
      ← MonoidHom.mem_ker, hφk]
    exact Subgroup.mem_subgroupOf.symm
  refine ⟨g, orderOf_eq_prime ?_ ?_⟩
  · rw [← map_pow, hker, map_pow, hg, ← hy]
    exact pow_orderOf_eq_one y
  · rw [Ne, hker, hg]
    intro h1
    rw [h1] at hy
    simp at hy

theorem Setting.psi_orderOf_ne_five (hB69 : B69Struct) (hB1 : B69One) (h : Setting H T M₂ U A)
    {L₀ N₀ : Subgroup G} (hstep₀ : IsChiefStep H U L₀ N₀) (hnc₀ : ¬ IsCentralStep H L₀ N₀)
    {χ₀ : ↥H →* ℤˣ} (hχC : ∀ g : ↥H, (g : G) ∈ centralizerMod L₀ H N₀ → χ₀ g = 1)
    {a : G} (haA : a ∈ A) (haH : a ∈ H) (hχa : χ₀ ⟨a, haH⟩ = -1)
    (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N)
    {M V : Subgroup G} (hM₂ : M₂ ≤ M) (hAV : A ≤ Subgroup.centralizer (V : Set G))
    (hMV : ∀ g ∈ M₂, g ∈ Subgroup.normalizer (V : Set G)) (hNo3 : NoThreeInCV M V) :
    ∀ g : ↥H, orderOf (chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) g) ≠ 5 := by
  intro g hg5
  have hHL := Setting.hHL hstep
  have hHN := Setting.hHN hstep
  have hE := h.hE hstep
  have hNL := h.hNL hstep
  let _ : CommGroup ↥(chiefMod L N) := chiefCG hE
  obtain ⟨𝓗, hctx⟩ := h.blkCtx hB69 hstep hnc
  have hsym := h.symBlk_all hB1 hstep₀ hnc₀ hχC haA haH hχa hstep hnc hctx
  have hstrong := h.noStrong hB1 hstep hnc
  obtain ⟨hAe, hA1, hoff⟩ := h.offender hstep hnc
  set D : Subgroup (MulAut ↥(chiefMod L N)) :=
    chiefImg hHL hHN (M₂ ⊓ Subgroup.centralizer (V : Set G)) with hD
  have hAT : chiefImg hHL hHN A ≤ chiefImg hHL hHN T := chiefImg_mono' hHL hHN h.AT.1
  have hAD : chiefImg hHL hHN A ≤ D :=
    chiefImg_mono' hHL hHN (le_inf (h.AT.1.trans h.mp.le) hAV)
  have hDM : ∀ x ∈ chiefImg hHL hHN M₂, ∀ d ∈ D, x * d * x⁻¹ ∈ D := by
    intro x hx d hd
    obtain ⟨g₀, hg₀, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨d₀, hd₀, rfl⟩ := Subgroup.mem_map.mp hd
    have hg₀' : (g₀ : G) ∈ M₂ := Subgroup.mem_subgroupOf.mp hg₀
    have hd₀' := Subgroup.mem_subgroupOf.mp hd₀
    refine Subgroup.mem_map.mpr ⟨g₀ * d₀ * g₀⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
    refine ⟨M₂.mul_mem (M₂.mul_mem hg₀' hd₀'.1) (M₂.inv_mem hg₀'), ?_⟩
    exact conj_mem_centralizer (hMV _ hg₀') hd₀'.2
  have hD3 : ∀ d ∈ D, ¬ 3 ∣ orderOf d := by
    intro d hd h3
    obtain ⟨d₀, hd₀, rfl⟩ := Subgroup.mem_map.mp hd
    have hd₀' : (d₀ : G) ∈ M₂ ⊓ Subgroup.centralizer (V : Set G) := Subgroup.mem_subgroupOf.mp hd₀
    have h3' : 3 ∣ orderOf (d₀ : G) := by
      refine h3.trans ?_
      rw [Subgroup.orderOf_coe]
      exact orderOf_map_dvd _ _
    obtain ⟨n, hn⟩ := h3'
    have hn0 : n ≠ 0 := by
      rintro rfl
      have := orderOf_pos (d₀ : G)
      omega
    have hord : orderOf ((d₀ : G) ^ n) = 3 := by
      rw [orderOf_pow_of_dvd hn0 ⟨3, by rw [hn]; ring⟩, hn]
      exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hn0)
    have hy : (d₀ : G) ^ n ∈ Subgroup.centralizer (V : Set G) :=
      Subgroup.pow_mem _ hd₀'.2 n
    refine hNo3 ((d₀ : G) ^ n) (hM₂ (M₂.pow_mem hd₀'.1 n)) (fun v hv => ?_) hord
    have h1 := (Subgroup.mem_centralizer_iff.mp hy) v hv
    calc (d₀ : G) ^ n * v * ((d₀ : G) ^ n)⁻¹ = (v * (d₀ : G) ^ n) * ((d₀ : G) ^ n)⁻¹ := by rw [h1]
      _ = v := by group
  have key := BlkCtx.orderOf_ne_five hctx (h.rank hstep) hsym hstrong hAT hAe hA1 hoff hAD hDM hD3
  have hmem : chiefPsi hHL hHN g ∈ ffJ (chiefAut H L N) :=
    Ch3w.odd_mem_ffJ hctx (chiefPsi_mem hHL hHN g) (by rw [hg5]; decide)
  exact key _ hmem hg5

end Chief

section Order

theorem orderOf_finRotate_five : orderOf (finRotate 5) = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem orderOf_wrI₁_finRotate_five :
    orderOf (wrI₁ (finRotate 5) : Equiv.Perm (Fin 5) ≀ᵣ Multiplicative (ZMod 2)) = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · have h5 : (finRotate 5) ^ 5 = (1 : Equiv.Perm (Fin 5)) := by decide
    have := congrArg (Ch3w.wrI₁hom (D := Equiv.Perm (Fin 5))) h5
    rw [map_pow, map_one] at this
    exact this
  · intro h1
    have h2 := congrArg (fun w : Equiv.Perm (Fin 5) ≀ᵣ Multiplicative (ZMod 2) => w.left 1) h1
    have h3 : (finRotate 5 : Equiv.Perm (Fin 5)) = 1 := by simpa [wrI₁] using h2
    exact absurd h3 (by decide)

end Order

section Main

theorem lemma319NoS5_of_good (hB69 : B69Struct) (hB1 : B69One) (hgood : Lemma319SixGood) :
    Lemma319NoS5 := by
  intro G _ _ T hs hnab hK hT M M₀ H V hM hbase hII hq hMu hVH hdual hconcl h6i h6iii hNo3 L N
    hstep hnc
  have h : Hyp319 T M M₀ H V := ⟨hbase, hII, hq, hMu, hVH, fun hd => hdual ⟨_, hd⟩⟩
  have hD := h.d11Hyp hT
  have hnff : ¬ IsFFInt M₀ V h.reduced.2.2.1 := fun hff =>
    h.not_qInt_le_one ((isFFInt_iff_qInt_le_one _ _ _).mp hff)
  have hmp : MinParabolic H T (H ⊓ M) := hD.minParabolic hnff
  have hsq : IsSQTKSub H := isSQTKSub_of_inH hK hs hnab h.inH_H
  have hUe := hconcl.elemAbelian
  have hUT : conjClosure V H ≤ T := conjClosure_le_T hD h.le_pCore
  have hRT := h.pCoreOf_le hT
  obtain ⟨A, hA⟩ := hconcl.exists_A
  have hset : Setting H T (H ⊓ M) (conjClosure V H) A :=
    ⟨hmp, hsq, hUT, hUe, hA.1, hA.not_le hRT,
      fun L' N' hs' hnc' => hconcl.count_four A hA L' N' hs' hnc'⟩
  obtain ⟨L₀, N₀, hstep₀, hnc₀, χ₀, hχC, a, haA, haH, hχa⟩ :=
    hgood G T hs hnab hK hT M M₀ H V hM hbase hII hq hMu hVH hdual hconcl h6i h6iii A hA
  have hno5 := Setting.psi_orderOf_ne_five hB69 hB1 hset hstep₀ hnc₀ hχC haA haH hχa hstep hnc
    (inf_le_right : H ⊓ M ≤ M) (IsMinOffender.le_centralizer hT h hA) (fun g hg => hII hg) hNo3
  refine ⟨?_, ?_⟩
  · rintro ⟨hnorm, ⟨φ, hφs, hφk, -⟩, -⟩
    obtain ⟨g, hg⟩ := exists_psi_orderOf_five hset hstep φ hφs hφk orderOf_finRotate_five
    exact hno5 g hg
  · rintro ⟨hnorm, ⟨φ, hφs, hφk, -⟩, -⟩
    obtain ⟨g, hg⟩ := exists_psi_orderOf_five hset hstep φ hφs hφk orderOf_wrI₁_finRotate_five
    exact hno5 g hg

end Main

end CFSG.Quasithin.H13.L319
