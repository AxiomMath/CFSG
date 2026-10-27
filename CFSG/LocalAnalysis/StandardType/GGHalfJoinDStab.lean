module

public import CFSG.LocalAnalysis.StandardType.GGHalfJoinSigned
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylBasic
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylRank
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylAutomizer
public import CFSG.LocalAnalysis.StandardType.GGHalfTorusFrame
public import CFSG.LocalAnalysis.StandardType.GGSpFrameIso
public import CFSG.LocalAnalysis.StandardType.GGSpFrameOrbit
public import CFSG.LocalAnalysis.StandardType.GGSpJoinOrbitBound

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem eq_or_inv_of_card_three {H : Type*} [Group H] (hH : Nat.card H = 3)
    {u u' : H} (hu : u ≠ 1) (hu' : u' ≠ 1) : u' = u ∨ u' = u⁻¹ := by
  classical
  haveI : Finite H := Nat.finite_of_card_ne_zero (by omega)
  have hu3 : orderOf u = 3 := by
    have h1 : orderOf u ∣ 3 := hH ▸ orderOf_dvd_natCard u
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hu
    · exact h
  have htop : Subgroup.zpowers u = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hu3, hH]
  have hmem : u' ∈ Subgroup.zpowers u := htop ▸ Subgroup.mem_top u'
  rw [mem_zpowers_iff_mem_range_orderOf, hu3] at hmem
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hmem
  have hk3 : k < 3 := Finset.mem_range.1 hk
  have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk_cases with rfl | rfl | rfl
  · exact absurd (pow_zero u) hu'
  · exact Or.inl (pow_one u)
  · refine Or.inr ?_
    have h3 : u ^ 3 = 1 := hu3 ▸ pow_orderOf_eq_one u
    exact eq_inv_of_mul_eq_one_right (by simpa [← pow_succ'] using h3)

private theorem zmod3_eq_or_inv (u u' : Multiplicative (ZMod 3)) (hu : u ≠ 1) (hu' : u' ≠ 1) :
    u' = u ∨ u' = u⁻¹ := by
  have hcard : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  exact eq_or_inv_of_card_three hcard hu hu'

private theorem exists_mulSingle_of_pairwise {n : ℕ} {M : Type*} [Group M] {v : Fin n → M}
    (hv : v ≠ 1) (h : ∀ i j : Fin n, i ≠ j → v i = 1 ∨ v j = 1) :
    ∃ i : Fin n, ∃ u : M, u ≠ 1 ∧ v = Pi.mulSingle i u := by
  classical
  have hex : ∃ i, v i ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hv (funext fun i => by simpa using hc i)
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, v i, hi, ?_⟩
  funext t
  by_cases ht : t = i
  · subst ht; simp
  · have hne : i ≠ t := fun hh => ht hh.symm
    rcases h i t hne with h1 | h1
    · exact absurd h1 hi
    · simp [Pi.mulSingle_eq_of_ne ht, h1]

private lemma mulSingle_mem_zpowers {n : ℕ} {i : Fin n} {u : Multiplicative (ZMod 3)}
    (hu : u ≠ 1) (a : Multiplicative (ZMod 3)) :
    Pi.mulSingle i a ∈ Subgroup.zpowers (Pi.mulSingle i u : Fin n → Multiplicative (ZMod 3)) := by
  by_cases ha : a = 1
  · rw [ha, Pi.mulSingle_one]
    exact Subgroup.one_mem _
  · rcases zmod3_eq_or_inv u a hu ha with h | h
    · rw [h]
      exact Subgroup.mem_zpowers _
    · have hau : (Pi.mulSingle i a : Fin n → Multiplicative (ZMod 3)) =
          (Pi.mulSingle i u : Fin n → Multiplicative (ZMod 3))⁻¹ := by
        rw [h]
        exact Pi.mulSingle_inv (f := fun _ => Multiplicative (ZMod 3)) i u
      rw [hau]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)

private lemma eq_mulSingle_mul_mulSingle {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {z : Fin n → Multiplicative (ZMod 3)}
    (hz : ∀ l, l ≠ i → l ≠ j → z l = 1) :
    z = Pi.mulSingle i (z i) * Pi.mulSingle j (z j) := by
  funext l
  by_cases hli : l = i
  · subst hli
    rw [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij, mul_one]
  · by_cases hlj : l = j
    · subst hlj
      rw [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hli, one_mul]
    · rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hli, Pi.mulSingle_eq_of_ne hlj, one_mul]
      exact hz l hli hlj

private def coordSupported {n : ℕ} (i j : Fin n) :
    Subgroup (Fin n → Multiplicative (ZMod 3)) where
  carrier := {z | ∀ l, l ≠ i → l ≠ j → z l = 1}
  mul_mem' := by
    intro a b ha hb l hli hlj
    simp [Pi.mul_apply, ha l hli hlj, hb l hli hlj]
  one_mem' := by
    intro l _ _
    rfl
  inv_mem' := by
    intro a ha l hli hlj
    change (a l)⁻¹ = 1
    rw [ha l hli hlj]
    exact inv_one

theorem GGHalfWeylCtx.joinDStab {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {m : ℕ} {y : G} {K : Subgroup G}
    (h : GGHalfWeylCtx p B Bs x L D J m y K) (hAut : GGHalfAutWithin Bs L K)
    {y' : G} (hy'D : y' ∈ D) (hy'Bs : y' ∈ Bs) (hy'x : y' ∉ Subgroup.zpowers x)
    (hy'y : y' ∉ Subgroup.zpowers y) {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced ⊤ Bs)
    (hfix : ((φ ⟨y', hy'Bs⟩ : ↥Bs) : G) = y') :
    ∀ b : ↥Bs, (b : G) ∈ D → ((φ b : ↥Bs) : G) ∈ D := by
  obtain ⟨-, -, hxBs, hyBs, hx1, hy1, hLx, hKy, -, -⟩ := h.basic
  obtain rfl : p = 3 := h.p_eq
  have hBsEA : IsElemAbelian 3 Bs := h.cfg.2.1.2.1
  obtain ⟨ψL, ψK, hL, hK⟩ := h.exists_frames (@ggHalf_torusFrame)
  obtain ⟨-, -, -, -, hnbr, -, r, hr⟩ := h.nbr
  let k := (m + 1 + 1 + 1) / 2
  have hrk : r = k + 1 := h.weylRank_eq hL hK hr
  rw [hrk] at hr
  have hk3 : 3 ≤ k := by
    have := h.five_le
    dsimp [k]; omega
  have hcard : Nat.card Bs = 3 ^ (k + 1) := h.card_bs hL
  have hcardL : 2 ^ k * k.factorial ≤ Nat.card (ggAutomizer L Bs) :=
    hL.card_automizer_ge (by omega)
  have hcardK : 2 ^ k * k.factorial ≤ Nat.card (ggAutomizer K Bs) :=
    hK.card_automizer_ge (by omega)
  obtain ⟨Φ, hΦ⟩ := SpFrame.exists_frame_iso_of_weyl (p := 3) (m := k) Nat.prime_three
    (by norm_num) hBsEA (by omega) hcard hr
  have hxLcent : x ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun l hl => (hLx l hl).symm
  have hyKcent : y ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun kk hk => (hKy kk hk).symm
  have hfixX : ∀ ψ ∈ ggAutomizer L Bs, ((ψ ⟨x, hxBs⟩ : ↥Bs) : G) = x :=
    SpJoin.ggAutomizer_fixes_of_mem_centralizer hxBs hxLcent
  have hfixY : ∀ ψ ∈ ggAutomizer K Bs, ((ψ ⟨y, hyBs⟩ : ↥Bs) : G) = y :=
    SpJoin.ggAutomizer_fixes_of_mem_centralizer hyBs hyKcent
  let v : Fin (k + 1) → Multiplicative (ZMod 3) := Φ.symm ⟨x, hxBs⟩
  let w : Fin (k + 1) → Multiplicative (ZMod 3) := Φ.symm ⟨y, hyBs⟩
  have hv : v ≠ 1 := by
    intro hv1
    have h1 : (⟨x, hxBs⟩ : ↥Bs) = 1 := by
      have hΦv : Φ v = (⟨x, hxBs⟩ : ↥Bs) := Φ.apply_symm_apply ⟨x, hxBs⟩
      rw [hv1, map_one] at hΦv
      exact hΦv.symm
    exact hx1 (Subtype.ext_iff.mp h1)
  have hw : w ≠ 1 := by
    intro hw1
    have h1 : (⟨y, hyBs⟩ : ↥Bs) = 1 := by
      have hΦw : Φ w = (⟨y, hyBs⟩ : ↥Bs) := Φ.apply_symm_apply ⟨y, hyBs⟩
      rw [hw1, map_one] at hΦw
      exact hΦw.symm
    exact hy1 (Subtype.ext_iff.mp h1)
  have hpairv : ∀ i j : Fin (k + 1), i ≠ j → v i = 1 ∨ v j = 1 := by
    intro i j hij
    exact SpFrame.coord_eq_one_of_fixed (p := 3) (m := k) Nat.prime_three (by norm_num) hk3
      (A := ggAutomizer L Bs ⊔ ggAutomizer K Bs) hr Φ hΦ
      (H := ggAutomizer L Bs) le_sup_left hxBs hfixX hcardL hij
  have hpairw : ∀ i j : Fin (k + 1), i ≠ j → w i = 1 ∨ w j = 1 := by
    intro i j hij
    exact SpFrame.coord_eq_one_of_fixed (p := 3) (m := k) Nat.prime_three (by norm_num) hk3
      (A := ggAutomizer L Bs ⊔ ggAutomizer K Bs) hr Φ hΦ
      (H := ggAutomizer K Bs) le_sup_right hyBs hfixY hcardK hij
  obtain ⟨i, u, hu, hv_eq⟩ := exists_mulSingle_of_pairwise hv hpairv
  obtain ⟨j, u', hu', hw_eq⟩ := exists_mulSingle_of_pairwise hw hpairw
  have hij : i ≠ j := by
    intro hij
    have hw_zp : w ∈ Subgroup.zpowers v := by
      rw [hw_eq, hv_eq, ← hij]
      exact mulSingle_mem_zpowers (i := i) (u := u) hu u'
    have hy_zx_sub : (⟨y, hyBs⟩ : ↥Bs) ∈ Subgroup.zpowers (⟨x, hxBs⟩ : ↥Bs) := by
      have hmem : Φ w ∈ Subgroup.zpowers (Φ v) := by
        have h1 : Φ w ∈ Subgroup.map (Φ : (Fin (k + 1) → Multiplicative (ZMod 3)) →* ↥Bs)
            (Subgroup.zpowers v) := Subgroup.mem_map.mpr ⟨w, hw_zp, rfl⟩
        rwa [MonoidHom.map_zpowers] at h1
      have hy_eq : (⟨y, hyBs⟩ : ↥Bs) = Φ w := (Φ.apply_symm_apply ⟨y, hyBs⟩).symm
      have hx_eq : (⟨x, hxBs⟩ : ↥Bs) = Φ v := (Φ.apply_symm_apply ⟨x, hxBs⟩).symm
      rw [hy_eq, hx_eq]
      exact hmem
    have hy_zx : y ∈ Subgroup.zpowers x := by
      have h1 : y ∈ Subgroup.map Bs.subtype (Subgroup.zpowers (⟨x, hxBs⟩ : ↥Bs)) :=
        Subgroup.mem_map.mpr ⟨⟨y, hyBs⟩, hy_zx_sub, rfl⟩
      rwa [MonoidHom.map_zpowers] at h1
    have hycent : y ∈ Subgroup.centralizer (L : Set G) :=
      Subgroup.zpowers_le.mpr hxLcent hy_zx
    exact h.not_centralizes_L (fun l hl => (Subgroup.mem_centralizer_iff.mp hycent l hl).symm)
  let S : Subgroup (Fin (k + 1) → Multiplicative (ZMod 3)) := coordSupported i j
  let Sbs : Subgroup ↥Bs := S.map (Φ : (Fin (k + 1) → Multiplicative (ZMod 3)) →* ↥Bs)
  let T : Subgroup G := Sbs.map Bs.subtype
  have hmemSbs : ∀ b : ↥Bs, b ∈ Sbs ↔ Φ.symm b ∈ S := by
    intro b
    constructor
    · intro hb
      obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp hb
      have ha' : a = Φ.symm b := Φ.injective (haeq.trans (Φ.apply_symm_apply b).symm)
      rw [ha'] at ha
      exact ha
    · intro hb
      exact Subgroup.mem_map.mpr ⟨Φ.symm b, hb, Φ.apply_symm_apply b⟩
  have hTmem : ∀ b : ↥Bs, ((b : G) ∈ T) ↔ b ∈ Sbs := by
    intro b
    constructor
    · intro hb
      obtain ⟨c, hc, hceq⟩ := Subgroup.mem_map.mp hb
      have hcb : c = b := Subtype.ext hceq
      rwa [hcb] at hc
    · intro hb
      exact Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
  have hΦei : Φ (Pi.mulSingle i u) = (⟨x, hxBs⟩ : ↥Bs) := by
    rw [← hv_eq]; exact Φ.apply_symm_apply ⟨x, hxBs⟩
  have hΦej : Φ (Pi.mulSingle j u') = (⟨y, hyBs⟩ : ↥Bs) := by
    rw [← hw_eq]; exact Φ.apply_symm_apply ⟨y, hyBs⟩
  have hxD : x ∈ D := by rw [hnbr.2.1]; exact Subgroup.subset_closure (by simp)
  have hyD : y ∈ D := by rw [hnbr.2.1]; exact Subgroup.subset_closure (by simp)
  have hxT : x ∈ T := by
    have hb : (⟨x, hxBs⟩ : ↥Bs) ∈ Sbs := by
      rw [hmemSbs]
      change ∀ l, l ≠ i → l ≠ j → (Φ.symm ⟨x, hxBs⟩) l = 1
      intro l hl _
      rw [show Φ.symm ⟨x, hxBs⟩ = Pi.mulSingle i u from hv_eq, Pi.mulSingle_eq_of_ne hl]
    exact Subgroup.mem_map.mpr ⟨⟨x, hxBs⟩, hb, rfl⟩
  have hyT : y ∈ T := by
    have hb : (⟨y, hyBs⟩ : ↥Bs) ∈ Sbs := by
      rw [hmemSbs]
      change ∀ l, l ≠ i → l ≠ j → (Φ.symm ⟨y, hyBs⟩) l = 1
      intro l _ hl
      rw [show Φ.symm ⟨y, hyBs⟩ = Pi.mulSingle j u' from hw_eq, Pi.mulSingle_eq_of_ne hl]
    exact Subgroup.mem_map.mpr ⟨⟨y, hyBs⟩, hb, rfl⟩
  have hDT : D ≤ T := by
    rw [hnbr.2.1]
    apply (Subgroup.closure_le T).mpr
    intro z hz
    rcases hz with rfl | rfl
    · exact hxT
    · exact hyT
  have hz0Sbs : (⟨y', hy'Bs⟩ : ↥Bs) ∈ Sbs := (hTmem ⟨y', hy'Bs⟩).mp (hDT hy'D)
  have hz0S' : ∀ l, l ≠ i → l ≠ j → (Φ.symm ⟨y', hy'Bs⟩) l = 1 :=
    (hmemSbs ⟨y', hy'Bs⟩).mp hz0Sbs
  have hz0i : (Φ.symm ⟨y', hy'Bs⟩) i ≠ 1 := by
    intro hzi
    have hz0_eq : Φ.symm ⟨y', hy'Bs⟩ = Pi.mulSingle j ((Φ.symm ⟨y', hy'Bs⟩) j) := by
      funext l
      by_cases hli : l = i
      · rw [hli]
        rw [Pi.mulSingle_eq_of_ne hij]
        exact hzi
      · by_cases hlj : l = j
        · rw [hlj]
          rw [Pi.mulSingle_eq_same]
        · rw [Pi.mulSingle_eq_of_ne hlj]
          exact hz0S' l hli hlj
    have hmemZ : Φ (Pi.mulSingle j ((Φ.symm ⟨y', hy'Bs⟩) j)) ∈
        Subgroup.zpowers (⟨y, hyBs⟩ : ↥Bs) := by
      have h1 := mulSingle_mem_zpowers (i := j) (u := u') hu' ((Φ.symm ⟨y', hy'Bs⟩) j)
      have h : Φ (Pi.mulSingle j ((Φ.symm ⟨y', hy'Bs⟩) j)) ∈
          Subgroup.map (Φ : (Fin (k + 1) → Multiplicative (ZMod 3)) →* ↥Bs)
            (Subgroup.zpowers (Pi.mulSingle j u')) :=
        (Subgroup.mem_map (f := (Φ : (Fin (k + 1) → Multiplicative (ZMod 3)) →* ↥Bs))).mpr
          ⟨Pi.mulSingle j ((Φ.symm ⟨y', hy'Bs⟩) j), h1, rfl⟩
      rw [MonoidHom.map_zpowers] at h
      simpa [hΦej] using h
    have h3 : ((Φ (Pi.mulSingle j ((Φ.symm ⟨y', hy'Bs⟩) j)) : ↥Bs) : G) ∈
        Subgroup.zpowers y := by
      have h : ((Φ (Pi.mulSingle j ((Φ.symm ⟨y', hy'Bs⟩) j)) : ↥Bs) : G) ∈
          Subgroup.map Bs.subtype (Subgroup.zpowers (⟨y, hyBs⟩ : ↥Bs)) :=
        Subgroup.mem_map.mpr ⟨Φ (Pi.mulSingle j ((Φ.symm ⟨y', hy'Bs⟩) j)), hmemZ, rfl⟩
      rw [MonoidHom.map_zpowers] at h
      simpa using h
    have hy'_mem : y' ∈ Subgroup.zpowers y := by
      have h4 : ((Φ (Pi.mulSingle j ((Φ.symm ⟨y', hy'Bs⟩) j)) : ↥Bs) : G) = y' := by
        rw [← hz0_eq, Φ.apply_symm_apply]
      rwa [h4] at h3
    exact hy'y hy'_mem
  have hz0j : (Φ.symm ⟨y', hy'Bs⟩) j ≠ 1 := by
    intro hzj
    have hz0_eq : Φ.symm ⟨y', hy'Bs⟩ = Pi.mulSingle i ((Φ.symm ⟨y', hy'Bs⟩) i) := by
      funext l
      by_cases hlj : l = j
      · rw [hlj]
        rw [Pi.mulSingle_eq_of_ne (fun h : j = i => hij h.symm)]
        exact hzj
      · by_cases hli : l = i
        · rw [hli]
          rw [Pi.mulSingle_eq_same]
        · rw [Pi.mulSingle_eq_of_ne hli]
          exact hz0S' l hli hlj
    have hmemZ : Φ (Pi.mulSingle i ((Φ.symm ⟨y', hy'Bs⟩) i)) ∈
        Subgroup.zpowers (⟨x, hxBs⟩ : ↥Bs) := by
      have h1 := mulSingle_mem_zpowers (i := i) (u := u) hu ((Φ.symm ⟨y', hy'Bs⟩) i)
      have h : Φ (Pi.mulSingle i ((Φ.symm ⟨y', hy'Bs⟩) i)) ∈
          Subgroup.map (Φ : (Fin (k + 1) → Multiplicative (ZMod 3)) →* ↥Bs)
            (Subgroup.zpowers (Pi.mulSingle i u)) :=
        (Subgroup.mem_map (f := (Φ : (Fin (k + 1) → Multiplicative (ZMod 3)) →* ↥Bs))).mpr
          ⟨Pi.mulSingle i ((Φ.symm ⟨y', hy'Bs⟩) i), h1, rfl⟩
      rw [MonoidHom.map_zpowers] at h
      simpa [hΦei] using h
    have h3 : ((Φ (Pi.mulSingle i ((Φ.symm ⟨y', hy'Bs⟩) i)) : ↥Bs) : G) ∈
        Subgroup.zpowers x := by
      have h : ((Φ (Pi.mulSingle i ((Φ.symm ⟨y', hy'Bs⟩) i)) : ↥Bs) : G) ∈
          Subgroup.map Bs.subtype (Subgroup.zpowers (⟨x, hxBs⟩ : ↥Bs)) :=
        Subgroup.mem_map.mpr ⟨Φ (Pi.mulSingle i ((Φ.symm ⟨y', hy'Bs⟩) i)), hmemZ, rfl⟩
      rw [MonoidHom.map_zpowers] at h
      simpa using h
    have hy'_mem : y' ∈ Subgroup.zpowers x := by
      have h4 : ((Φ (Pi.mulSingle i ((Φ.symm ⟨y', hy'Bs⟩) i)) : ↥Bs) : G) = y' := by
        rw [← hz0_eq, Φ.apply_symm_apply]
      rwa [h4] at h3
    exact hy'x hy'_mem
  obtain ⟨g, hg_mem, hgval⟩ := GGHalfJoin.frame_upper hr Φ hΦ φ (hAut φ hφ)
  have hgz : g (Φ.symm ⟨y', hy'Bs⟩) = Φ.symm ⟨y', hy'Bs⟩ := by
    apply Φ.injective
    apply Subtype.ext
    have h1 : ((Φ (g (Φ.symm ⟨y', hy'Bs⟩)) : ↥Bs) : G) = y' := by
      have h := hgval (Φ.symm ⟨y', hy'Bs⟩)
      rw [Φ.apply_symm_apply] at h
      rw [← h]
      exact hfix
    have h2 : ((Φ (Φ.symm ⟨y', hy'Bs⟩) : ↥Bs) : G) = y' := by
      rw [Φ.apply_symm_apply]
    exact h1.trans h2.symm
  intro b hbD
  have hzbSbs : b ∈ Sbs := (hTmem b).mp (hDT hbD)
  have hzbS' : ∀ l, l ≠ i → l ≠ j → (Φ.symm b) l = 1 := (hmemSbs b).mp hzbSbs
  have hg_pres : ∀ l, l ≠ i → l ≠ j → g (Φ.symm b) l = 1 :=
    GGHalfJoin.signed_preserves_support (n := k + 1) hg_mem hij hz0i hz0j hz0S' hgz hzbS'
  have hsplit : g (Φ.symm b) =
      Pi.mulSingle i ((g (Φ.symm b)) i) * Pi.mulSingle j ((g (Φ.symm b)) j) :=
    eq_mulSingle_mul_mulSingle hij hg_pres
  have hfac_i : ((Φ (Pi.mulSingle i ((g (Φ.symm b)) i)) : ↥Bs) : G) ∈ D := by
    have h1 := mulSingle_mem_zpowers (i := i) (u := u) hu ((g (Φ.symm b)) i)
    have h2 : Φ (Pi.mulSingle i ((g (Φ.symm b)) i)) ∈ Subgroup.zpowers (⟨x, hxBs⟩ : ↥Bs) := by
      have h : Φ (Pi.mulSingle i ((g (Φ.symm b)) i)) ∈
          Subgroup.map (Φ : (Fin (k + 1) → Multiplicative (ZMod 3)) →* ↥Bs)
            (Subgroup.zpowers (Pi.mulSingle i u)) :=
        (Subgroup.mem_map (f := (Φ : (Fin (k + 1) → Multiplicative (ZMod 3)) →* ↥Bs))).mpr
          ⟨Pi.mulSingle i ((g (Φ.symm b)) i), h1, rfl⟩
      rw [MonoidHom.map_zpowers] at h
      simpa [hΦei] using h
    have h3 : ((Φ (Pi.mulSingle i ((g (Φ.symm b)) i)) : ↥Bs) : G) ∈ Subgroup.zpowers x := by
      have h : ((Φ (Pi.mulSingle i ((g (Φ.symm b)) i)) : ↥Bs) : G) ∈
          Subgroup.map Bs.subtype (Subgroup.zpowers (⟨x, hxBs⟩ : ↥Bs)) :=
        Subgroup.mem_map.mpr ⟨Φ (Pi.mulSingle i ((g (Φ.symm b)) i)), h2, rfl⟩
      rw [MonoidHom.map_zpowers] at h
      simpa using h
    exact Subgroup.zpowers_le.mpr hxD h3
  have hfac_j : ((Φ (Pi.mulSingle j ((g (Φ.symm b)) j)) : ↥Bs) : G) ∈ D := by
    have h1 := mulSingle_mem_zpowers (i := j) (u := u') hu' ((g (Φ.symm b)) j)
    have h2 : Φ (Pi.mulSingle j ((g (Φ.symm b)) j)) ∈ Subgroup.zpowers (⟨y, hyBs⟩ : ↥Bs) := by
      have h : Φ (Pi.mulSingle j ((g (Φ.symm b)) j)) ∈
          Subgroup.map (Φ : (Fin (k + 1) → Multiplicative (ZMod 3)) →* ↥Bs)
            (Subgroup.zpowers (Pi.mulSingle j u')) :=
        (Subgroup.mem_map (f := (Φ : (Fin (k + 1) → Multiplicative (ZMod 3)) →* ↥Bs))).mpr
          ⟨Pi.mulSingle j ((g (Φ.symm b)) j), h1, rfl⟩
      rw [MonoidHom.map_zpowers] at h
      simpa [hΦej] using h
    have h3 : ((Φ (Pi.mulSingle j ((g (Φ.symm b)) j)) : ↥Bs) : G) ∈ Subgroup.zpowers y := by
      have h : ((Φ (Pi.mulSingle j ((g (Φ.symm b)) j)) : ↥Bs) : G) ∈
          Subgroup.map Bs.subtype (Subgroup.zpowers (⟨y, hyBs⟩ : ↥Bs)) :=
        Subgroup.mem_map.mpr ⟨Φ (Pi.mulSingle j ((g (Φ.symm b)) j)), h2, rfl⟩
      rw [MonoidHom.map_zpowers] at h
      simpa using h
    exact Subgroup.zpowers_le.mpr hyD h3
  have hgD : ((Φ (g (Φ.symm b)) : ↥Bs) : G) ∈ D := by
    rw [hsplit, map_mul, Subgroup.coe_mul]
    exact D.mul_mem hfac_i hfac_j
  have hφb : φ b = Φ (g (Φ.symm b)) := by
    have h := hgval (Φ.symm b)
    rwa [Φ.apply_symm_apply] at h
  rw [hφb]
  exact hgD

end CFSG.StandardType

end
