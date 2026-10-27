module

public import CFSG.RankThree.GF2n.Tim79a34TwDefs

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open scoped Matrix
open scoped commutatorElement

variable {G : Type} [Group G]

theorem twZR_mem_zpowers {X : Type} [Group X] {z : X} (hz2 : z * z = 1) {x : X}
    (hx : x ∈ Subgroup.zpowers z) : x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : ∀ m : ℤ, z ^ (2 * m) = 1 := fun m => by
    rw [zpow_mul, zpow_two, hz2, one_zpow]
  have hk : z ^ k = z ^ (k % 2) := by
    calc z ^ k = z ^ (k % 2 + 2 * (k / 2)) := by congr 1; omega
      _ = z ^ (k % 2) * z ^ (2 * (k / 2)) := zpow_add _ _ _
      _ = z ^ (k % 2) := by rw [h2, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [hk, h, zpow_zero]
  · right
    rw [hk, h, zpow_one]

theorem twZR_inf_zpowers_eq_bot {X : Type} [Group X] {R : Subgroup X} {z : X}
    (hz2 : z * z = 1) (hz : z ∉ R) : R ⊓ Subgroup.zpowers z = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxR, hxz⟩
  rcases twZR_mem_zpowers hz2 hxz with h | h
  · exact Subgroup.mem_bot.mpr h
  · rw [h] at hxR
    exact absurd hxR hz

theorem twZR_eq_of_quot_eq {X : Type} [Group X] {R Z : Subgroup X} [Z.Normal]
    (hRZ : R ⊓ Z = ⊥) {r s : X} (hr : r ∈ R) (hs : s ∈ R)
    (h : (QuotientGroup.mk r : X ⧸ Z) = QuotientGroup.mk s) : r = s := by
  have h1 : r⁻¹ * s ∈ R ⊓ Z := ⟨R.mul_mem (R.inv_mem hr) hs, QuotientGroup.eq.mp h⟩
  rw [hRZ, Subgroup.mem_bot, inv_mul_eq_one] at h1
  exact h1

theorem twZR_commutator_conj_mem {X : Type} [Group X] {k : X} (hk : k ∈ commutator X) (g : X) :
    g * k * g⁻¹ ∈ commutator X :=
  (show (commutator X).Normal from Subgroup.commutator_normal (⊤ : Subgroup X) ⊤).conj_mem k hk g

section SpPart

variable {n : ℕ} {F : Type} [Field F]

theorem twZR_exists_mat_mulVec_eq {a w : Fin n ⊕ Fin n → F} (ha : a ≠ 0) (hw : w ≠ 0) :
    ∃ g : StatedSp n F, SpExtras.mat n F g *ᵥ a = w := by
  obtain ⟨y₁, hy₁⟩ := ModelRank.exists_spForm_ne_zero ha
  obtain ⟨y₂, hy₂⟩ := ModelRank.exists_spForm_ne_zero hw
  obtain ⟨z, hz₁, hz₂⟩ : ∃ z : Fin n ⊕ Fin n → F,
      CaseM.spForm a z ≠ 0 ∧ CaseM.spForm w z ≠ 0 := by
    by_cases h2 : CaseM.spForm a y₂ = 0
    · by_cases h1 : CaseM.spForm w y₁ = 0
      · refine ⟨y₁ + y₂, ?_, ?_⟩
        · rw [ModelRank.spForm_add_right, h2, add_zero]
          exact hy₁
        · rw [ModelRank.spForm_add_right, h1, zero_add]
          exact hy₂
      · exact ⟨y₁, hy₁, h1⟩
    · exact ⟨y₂, h2, hy₂⟩
  obtain ⟨g₁, hg₁⟩ := ModelRank.exists_mat_mulVec_eq hz₁
  obtain ⟨g₂, hg₂⟩ := ModelRank.exists_mat_mulVec_eq (x := z) (y := w)
    (by rw [CaseM.spForm_comm]; exact neg_ne_zero.2 hz₂)
  refine ⟨g₂ * g₁, ?_⟩
  rw [map_mul, ← Matrix.mulVec_mulVec, hg₁, hg₂]

theorem twZR_spTrans_zero : CaseM.spTrans (0 : Fin n ⊕ Fin n → F) 1 = 1 := by
  simp [CaseM.spTrans, CaseM.spNil]

end SpPart

section MinCexPart

variable {M V Q P H : Subgroup G}

theorem twZR_conj_mem_inf [Finite G] (hc : MinCex M V Q P H) {y : ↥H}
    (hyM : (y : G) ∈ M) {z : Xbar V H} (hz : (z : Hbar V H) = piBar V H y)
    {r : Xbar V H} (hr : r ∈ Rbar V H P ⊓ commutator (Xbar V H)) :
    z * r * z⁻¹ ∈ Rbar V H P ⊓ commutator (Xbar V H) := by
  obtain ⟨hrR, hrK⟩ := Subgroup.mem_inf.mp hr
  refine Subgroup.mem_inf.mpr ⟨?_, twZR_commutator_conj_mem hrK z⟩
  rw [mem_Rbar] at hrR ⊢
  obtain ⟨x, hxP, hx⟩ := mem_barOf_iff.mp hrR
  refine mem_barOf_iff.mpr ⟨y * x * y⁻¹, ?_, ?_⟩
  · have hN := (Subgroup.mem_normalizer_iff.mp (hc.M_le_normalizer_P hyM) (x : G)).mp hxP
    simpa using hN
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hz, ← hx]
    simp only [map_mul, map_inv]

theorem twZR_exists_conj_imgZ (hVH : V ≤ H) {n : ℕ} {F : Type} [Field F]
    {Φ : StatedSp n F →* XbarZ V H} {a w : Fin n ⊕ Fin n → F} {T : Subgroup (StatedSp n F)}
    (hT : CaseM.IsTransGroup a T) (hmap : T.map Φ = VZ V H) (ha : a ≠ 0) (hw : w ≠ 0) :
    ∃ Tw : Subgroup (StatedSp n F), CaseM.IsTransGroup w Tw ∧
      ∃ h : ↥(xOf V H), imgZ V H (conjSubgroup (h : G) V) = Tw.map Φ := by
  obtain ⟨g₀, hg₀⟩ := twZR_exists_mat_mulVec_eq ha hw
  refine ⟨CFSG.Timmesfeld.ARS.conjSub T g₀, ?_, ?_⟩
  · have h := hT.conjSub g₀
    rwa [hg₀] at h
  · obtain ⟨h, hh⟩ := xToZ_surjective hVH (Φ g₀)
    refine ⟨h, ?_⟩
    rw [imgZ_conj hVH h, hh, ← hmap]
    exact ModelRank.conjSub_map Φ T g₀

theorem twZR_mem_M_of_imgZ [Finite G] (hc : MinCex M V Q P H) {n : ℕ} {F : Type} [Field F]
    {Φ : StatedSp n F →* XbarZ V H} {a w : Fin n ⊕ Fin n → F} {T Tw : Subgroup (StatedSp n F)}
    (hT : CaseM.IsTransGroup a T) (hTw : CaseM.IsTransGroup w Tw)
    (haw : CaseM.spForm a w = 0) (hmap : T.map Φ = VZ V H) {h : ↥(xOf V H)}
    (hU : imgZ V H (conjSubgroup (h : G) V) = Tw.map Φ) :
    ∀ y ∈ conjSubgroup (h : G) V, y ∈ M := by
  have hcomm := hc.commute_conj_of_commute_tilde (x₁ := 1) (x₂ := h) (by
    intro a' ha' b' hb'
    rw [map_one, conjSubgroup_one] at ha'
    rw [← imgZ_conj hc.V_le_H h, hU] at hb'
    rw [← hmap] at ha'
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp ha'
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hb'
    rw [← map_mul, ← map_mul]
    exact congrArg Φ ((hT.commuting hTw haw t ht s hs).eq))
  intro y hy
  have hV : ∀ v ∈ V, v * y = y * v := fun v hv =>
    hcomm v (by rw [OneMemClass.coe_one, conjSubgroup_one]; exact hv) y hy
  have hcent : y ∈ Subgroup.centralizer (V : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun v hv => hV v hv
  have hN : y ∈ Subgroup.normalizer (V : Set G) := Subgroup.centralizer_le_normalizer _ hcent
  rw [hc.normalizer_eq] at hN
  exact hN

end MinCexPart

theorem twistedZR_holds (hB3 : NoInvCompStatement) : TwistedZRStatement := by
  intro G _ _ M V Q P H hs hS24 _hC n Φ a T z₀ hd
  by_contra hz0
  have hc : MinCex M V Q P H := hs.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hn : 3 ≤ n := hd.three_le
  have ha : a ≠ 0 := hd.ne_zero
  have hTa : CaseM.IsTransGroup a T := hd.trans
  have hmap : T.map Φ = VZ V H := hd.map_eq
  have hz2 : z₀ * z₀ = 1 := hd.z_sq
  have hZ : Subgroup.center (Xbar V H) = Subgroup.zpowers z₀ := hd.center_eq
  have hRad : (Rbar V H P).map (projZ V H) = (spRad a).map Φ := by
    have h1 : Rtilde V H P = pCoreOf 2 (Subgroup.normalizer
        ((T.map Φ : Subgroup (XbarZ V H)) : Set (XbarZ V H))) := by
      rw [hmap]
      exact hS24
    rw [pCoreOf_normalizer_map_of_bijective_pair Φ hd.bij T,
      spCoreStmt_holds n (GaloisField 2 1) ha hTa] at h1
    exact h1
  have hRb : Rbar V H P ⊓ Subgroup.center (Xbar V H) = ⊥ := by
    rw [hZ]
    exact twZR_inf_zpowers_eq_bot hz2 hz0
  have hinj : ∀ r ∈ Rbar V H P, ∀ s ∈ Rbar V H P, projZ V H r = projZ V H s → r = s :=
    fun r hr s hs h => twZR_eq_of_quot_eq hRb hr hs h
  obtain ⟨d, hdV, hdD, -⟩ := hc.exists_vy_mem_Dy hs.data
  have hdR : d ∈ Rbar V H P := hc.Vy_le_Rbar hdV
  have hdK : z₀ * d ∈ commutator (Xbar V H) := hd.D_mul d hdD
  have hz0inv : z₀⁻¹ = z₀ := inv_eq_of_mul_eq_one_right hz2
  have hdec : ∀ r ∈ Rbar V H P, r ∉ commutator (Xbar V H) →
      d⁻¹ * r ∈ commutator (Xbar V H) := by
    intro r _ hrK
    have hmem : r ∈ Subgroup.center (Xbar V H) ⊔ commutator (Xbar V H) := by
      rw [hd.sup_eq]
      exact Subgroup.mem_top r
    obtain ⟨c, hc', k, hk, hck⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    rw [hZ] at hc'
    rcases twZR_mem_zpowers hz2 hc' with h1 | h1
    · exfalso
      apply hrK
      rw [← hck, h1, one_mul]
      exact hk
    · rw [← hck, h1]
      have e : d⁻¹ * (z₀ * k) = (z₀ * d)⁻¹ * k := by
        rw [mul_inv_rev, hz0inv]
        simp only [mul_assoc]
      rw [e]
      exact (commutator (Xbar V H)).mul_mem ((commutator (Xbar V H)).inv_mem hdK) hk
  obtain ⟨S, hS⟩ : ∃ S : Subgroup (StatedSp n (GaloisField 2 1)),
      S = (((Rbar V H P) ⊓ commutator (Xbar V H)).map (projZ V H)).comap Φ := ⟨_, rfl⟩
  have hmemS : ∀ x, x ∈ S ↔
      ∃ r ∈ Rbar V H P ⊓ commutator (Xbar V H), projZ V H r = Φ x := by
    intro x
    rw [hS, Subgroup.mem_comap, Subgroup.mem_map]
  have hSle : S ≤ spRad a := by
    intro x hx
    obtain ⟨r, hr, hrx⟩ := (hmemS x).mp hx
    have h1 : Φ x ∈ (Rbar V H P).map (projZ V H) := by
      rw [← hrx]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_inf.mp hr).1
    rw [hRad] at h1
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h1
    have hxy : y = x := hd.bij.1 hyx
    rw [← hxy]
    exact hy
  have hsup : S ⊔ T = spRad a := by
    apply le_antisymm
    · exact sup_le hSle (ModelRank.le_spRad_of_isTransGroup hTa)
    · intro s hs
      have h1 : Φ s ∈ (Rbar V H P).map (projZ V H) := by
        rw [hRad]
        exact Subgroup.mem_map_of_mem Φ hs
      obtain ⟨r, hr, hrs⟩ := Subgroup.mem_map.mp h1
      by_cases hrK : r ∈ commutator (Xbar V H)
      · exact Subgroup.mem_sup_left ((hmemS s).mpr ⟨r, ⟨hr, hrK⟩, hrs⟩)
      · have hdT : projZ V H d ∈ T.map Φ := by
          rw [hmap]
          exact Subgroup.mem_map_of_mem _ hdV
        obtain ⟨t, ht, htd⟩ := Subgroup.mem_map.mp hdT
        have hmem : t⁻¹ * s ∈ S := by
          refine (hmemS (t⁻¹ * s)).mpr ⟨d⁻¹ * r, ⟨?_, hdec r hr hrK⟩, ?_⟩
          · exact (Rbar V H P).mul_mem ((Rbar V H P).inv_mem hdR) hr
          · simp only [map_mul, map_inv]
            rw [htd, hrs]
        have key : t * (t⁻¹ * s) ∈ T ⊔ S := Subgroup.mul_mem_sup ht hmem
        rw [mul_inv_cancel_left, sup_comm] at key
        exact key
  have hinf : S ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    rintro s ⟨hsS, hsT⟩
    obtain ⟨r, hr, hrs⟩ := (hmemS s).mp hsS
    have hsT' : Φ s ∈ VZ V H := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem Φ hsT
    obtain ⟨v, hv, hvs⟩ := Subgroup.mem_map.mp hsT'
    have hvR : v ∈ Rbar V H P := hc.Vy_le_Rbar hv
    have hrv : r = v := hinj r (Subgroup.mem_inf.mp hr).1 v hvR (hrs.trans hvs.symm)
    have hvK : v ∈ commutator (Xbar V H) := by
      rw [← hrv]
      exact (Subgroup.mem_inf.mp hr).2
    have hv1 : v = 1 := by
      by_contra hne
      have hv' : (v : Hbar V H) ∈ barOf V H V := Subgroup.mem_subgroupOf.mp hv
      have hne' : (v : Hbar V H) ≠ 1 := fun h => hne (Subtype.ext (by simpa using h))
      exact hd.D_not_comm v (hc.barOf_V_subset_dbarOf hv' hne') hvK
    have hΦs : Φ s = Φ 1 := by
      rw [map_one, ← hvs, hv1, map_one]
    exact Subgroup.mem_bot.mpr (hd.bij.1 hΦs)
  have hinv : ∀ (w : Fin n ⊕ Fin n → GaloisField 2 1)
      (g : ↥(StatedSp n (GaloisField 2 1))),
      CaseM.spForm a w = 0 → SpExtras.mat n (GaloisField 2 1) g = CaseM.spTrans w 1 →
        ∀ x ∈ S, g * x * g⁻¹ ∈ S := by
    intro w g hw hg x hx
    by_cases hw0 : w = 0
    · subst hw0
      have hg1 : g = 1 := SpExtras.mat_injective (by rw [hg, twZR_spTrans_zero, map_one])
      rw [hg1, one_mul, inv_one, mul_one]
      exact hx
    · obtain ⟨Tw, hTw, h, hU⟩ := twZR_exists_conj_imgZ hVH hTa hmap ha hw0
      have hMU := twZR_mem_M_of_imgZ hc hTa hTw hw hmap hU
      have hgTw : g ∈ Tw := (hTw.1 g).2 ⟨1, hg⟩
      have hΦg : Φ g ∈ imgZ V H (conjSubgroup (h : G) V) := by
        rw [hU]
        exact Subgroup.mem_map_of_mem Φ hgTw
      obtain ⟨z, hz, hzg⟩ := Subgroup.mem_map.mp hΦg
      obtain ⟨y, hyU, hyz⟩ := mem_barOf_iff.mp (Subgroup.mem_subgroupOf.mp hz)
      have hyM : (y : G) ∈ M := hMU y hyU
      obtain ⟨r, hr, hrx⟩ := (hmemS x).mp hx
      refine (hmemS (g * x * g⁻¹)).mpr ⟨z * r * z⁻¹, twZR_conj_mem_inf hc hyM hyz.symm hr, ?_⟩
      simp only [map_mul, map_inv]
      rw [hzg, hrx]
  have hF : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num)]
    norm_num
  exact hB3 n hn (GaloisField 2 1) hF a ha T S hTa hSle hsup hinf hinv

end CFSG.RankThree.GF2n.Tim79a
