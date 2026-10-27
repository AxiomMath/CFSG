module

public import CFSG.RankThree.PartOne.SEITZ6.G2Tor

public section

namespace CFSG.RankThree.PartOne.SEITZ6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.SEITZ3
  CFSG.LieType.RootSystem CFSG.Timmesfeld.RankTwo
open scoped commutatorElement

variable {K : Type} [Field K]

theorem refl_all : ∀ p < 12, ∀ i : Fin (Tag.rank .G2), ∃ p' < 12,
    reflect .G2 i (rt p) = rt p' := by decide +kernel

theorem weylAction_rt (w : (coxeterMatrix (g2Datum K).isFiniteType).Group) :
    ∀ p < 12, ∃ p' < 12, weylAction (g2Datum K).isFiniteType w (rt p) = rt p' := by
  obtain ⟨ω, -, rfl⟩ :=
    ((coxeterMatrix (g2Datum K).isFiniteType).toCoxeterSystem).exists_isReduced w
  induction ω with
  | nil =>
    intro p hp
    exact ⟨p, hp, by simp⟩
  | cons i l ih =>
    intro p hp
    obtain ⟨p', hp', h'⟩ := ih p hp
    obtain ⟨p'', hp'', h''⟩ := refl_all p' hp' i
    refine ⟨p'', hp'', ?_⟩
    rw [CoxeterSystem.wordProd_cons, weylAction_mul_apply, h',
      weylAction_simple_eq_reflect (g2Datum K).isFiniteType]
    exact h''

theorem root_pair_check : ∀ p < 12, ∀ q < 12, ∀ r < 12, ¬ ((∀ i, rt p i ≤ 0) ∧
    (∀ i, 2 * rt p i + 3 * rt q i = rt 7 i) ∧ (∀ i, rt r i = rt p i + rt q i)) := by
  decide +kernel

theorem reflect_e1_rt7 : reflect .G2 e1 (rt 7) = rt 7 := by decide +kernel

theorem rt7_lin : (rt 7 : Fin 2 → ℤ) = (2 : ℤ) • rt 0 + (3 : ℤ) • rt 1 := by
  ext i; fin_cases i <;> decide

theorem rt4_lin : (rt 4 : Fin 2 → ℤ) = rt 0 + rt 1 := by
  ext i; fin_cases i <;> decide

theorem weyl_stab_h (w : (coxeterMatrix (g2Datum K).isFiniteType).Group)
    (hw : weylAction (g2Datum K).isFiniteType w (rt 7) = rt 7) :
    w = 1 ∨ w = (coxeterMatrix (g2Datum K).isFiniteType).toCoxeterSystem.simple e1 := by
  set cs := (coxeterMatrix (g2Datum K).isFiniteType).toCoxeterSystem with hcs
  induction hn : cs.length w using Nat.strong_induction_on generalizing w with
  | _ n ih =>
  by_cases hw1 : w = 1
  · exact Or.inl hw1
  obtain ⟨i, hi⟩ := cs.exists_rightDescent_of_ne_one hw1
  fin_cases i
  · exfalso
    have hle := (isRightDescent_iff (g2Datum K).isFiniteType w e0).1 hi
    obtain ⟨p, hp, hpy⟩ := weylAction_rt (K := K) w 0 (by norm_num)
    obtain ⟨q, hq, hqx⟩ := weylAction_rt (K := K) w 1 (by norm_num)
    rw [← rt0_eq] at hle
    rw [hpy] at hle
    have hlin : weylAction (g2Datum K).isFiniteType w (rt 7) =
        (2 : ℤ) • weylAction (g2Datum K).isFiniteType w (rt 0) +
          (3 : ℤ) • weylAction (g2Datum K).isFiniteType w (rt 1) := by
      rw [← map_zsmul, ← map_zsmul, ← map_add]
      congr 1
      exact rt7_lin
    rw [hw, hpy, hqx] at hlin
    obtain ⟨r, hr, hrz⟩ := weylAction_rt (K := K) w 4 (by norm_num)
    have hlin4 : weylAction (g2Datum K).isFiniteType w (rt 4) =
        weylAction (g2Datum K).isFiniteType w (rt 0) +
          weylAction (g2Datum K).isFiniteType w (rt 1) := by
      rw [← map_add]
      congr 1
      exact rt4_lin
    rw [hrz, hpy, hqx] at hlin4
    exact root_pair_check p hp q hq r hr ⟨fun i => hle i, fun i => (congrFun hlin i).symm,
      fun i => congrFun hlin4 i⟩
  · have hlen : cs.length (w * cs.simple e1) + 1 = cs.length w := cs.isRightDescent_iff.1 hi
    have hw' : weylAction (g2Datum K).isFiniteType (w * cs.simple e1) (rt 7) = rt 7 := by
      rw [weylAction_mul_apply, weylAction_simple_eq_reflect (g2Datum K).isFiniteType,
        reflect_e1_rt7, hw]
    rcases ih _ (by omega) (w * cs.simple e1) hw' rfl with h | h
    · right
      have := eq_inv_of_mul_eq_one_left h
      rwa [cs.inv_simple] at this
    · exfalso
      exact hw1 (mul_right_cancel (h.trans (one_mul _).symm))

theorem posUnipotent_eq_Ug : posUnipotent (g2Datum K) = Ug K := by
  apply le_antisymm
  · refine iSup₂_le fun γ hγ => ?_
    obtain ⟨hγR, hγp⟩ := hγ
    obtain ⟨k, hk, rfl⟩ :=
      RootCertificate.exists_root_eq (Tag.rootCertificate_check .G2) (mem_g2_roots.1 hγR)
    have hk' : k < 12 := by simpa [len_roots] using hk
    have hkp := ht_pos_aux k hk' hγp
    refine le_iSup₂_of_le k ?_ le_rfl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hkp
    rcases hkp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [posList]
  · refine iSup₂_le fun p hp => ?_
    have hp' := lt_twelve_of_mem_posList hp
    have hr : rt p ∈ (g2Datum K).roots := mem_g2_roots.2 (isRoot_rt hp')
    have hpos : 0 < ht (rt p) := by
      rcases mem_posList hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    exact le_iSup₂_of_le (rt p) ⟨hr, hpos⟩ le_rfl

theorem Up_le_Ug : Up K ≤ Ug K := by
  refine sup_le ?_ ?_
  · exact le_iSup₂_of_le 7 (by simp [posList]) le_rfl
  · exact le_iSup₂_of_le 1 (by simp [posList]) le_rfl

theorem Ug_comm_xp7 [CharP K 2] {u : adjointGroup .G2 K} (hu : u ∈ Ug K) (c : K) :
    u * xp 7 c = xp 7 c * u := by
  have hle : Ug K ≤ Subgroup.centralizer ({xp 7 c} : Set (adjointGroup .G2 K)) := by
    refine iSup₂_le fun p hp => ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have hpm : p ∈ ({0, 1, 3, 4, 7, 8} : Finset ℕ) := by
      rcases mem_posList hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    exact ((commute_Xp_pos7 hpm x hx _ (xp_mem_Xp 7 (by norm_num) c)).eq).symm
  have := Subgroup.mem_centralizer_iff.1 (hle hu) (xp 7 c) (Set.mem_singleton _)
  exact this.symm

theorem xp_ne_one {p : ℕ} (hp : p < 12) {c : K} (hc : c ≠ 0) : xp p c ≠ 1 := fun h =>
  hc (xPar_injective (F := rootOperatorFamily .G2) (K := K) (isRoot_rt hp)
    (h.trans (xp_zero p).symm))

theorem rt_inj_check : ∀ p < 12, ∀ q < 12, rt p = rt q → p = q := by decide +kernel

theorem simple_inversion_check : ∀ k < 12, 0 < ht (rt k) →
    ht (reflect .G2 e1 (rt k)) < 0 → k = 1 := by decide +kernel

theorem inversionUnipotent_simple_le :
    inversionUnipotent (g2Datum K)
      ((coxeterMatrix (g2Datum K).isFiniteType).toCoxeterSystem.simple e1) ≤ Xp K 1 := by
  refine iSup₂_le fun γ hγ => ?_
  obtain ⟨hγR, hpos, hneg⟩ := hγ
  obtain ⟨k, hk, rfl⟩ :=
    RootCertificate.exists_root_eq (Tag.rootCertificate_check .G2) (mem_g2_roots.1 hγR)
  have hk' : k < 12 := by simpa [len_roots] using hk
  rw [weylAction_simple_eq_reflect (g2Datum K).isFiniteType] at hneg
  have := simple_inversion_check k hk' hpos hneg
  subst this
  exact le_rfl

theorem g2_bruhatExtras' : BruhatExtras (g2Datum K) (torus (τ := .G2) K) where
  borel_inf_negUnipotent := eq_bot_iff.2 ((inf_le_inf
    (sup_le (iSup_le fun i => (torus_le_diag i).trans (diag_le_tri htHom))
      ((iSup₂_le fun γ hγ => rootGroup_le_unip htHom hγ.2).trans (unip_le_tri htHom)))
    (iSup₂_le fun γ hγ => rootGroup_le_unip (-htHom) (by
      rw [AddMonoidHom.neg_apply, htHom_apply]
      exact neg_pos.2 hγ.2))).trans (tri_inf_unip_neg htHom).le)

theorem neg_root_not_mem_borel {t : ℕ} (ht12 : t < 12) (hneg : ht (rt t) < 0) {c : K}
    (hmem : xp t c ∈ borel (g2Datum K) (torus (τ := .G2) K)) : c = 0 := by
  have hBU := g2_bruhatExtras' (K := K)
  have h2 : xp t c ∈ negUnipotent (g2Datum K) :=
    rootGroup_le_negUnipotent (mem_g2_roots.2 (isRoot_rt ht12)) hneg (xp_mem_Xp t ht12 c)
  have h3 : xp t c ∈ borel (g2Datum K) (torus (τ := .G2) K) ⊓ negUnipotent (g2Datum K) :=
    ⟨hmem, h2⟩
  rw [hBU.borel_inf_negUnipotent, Subgroup.mem_bot] at h3
  by_contra hc
  exact xp_ne_one ht12 hc h3

theorem bruhat_stab_h [CharP K 2] {g : adjointGroup .G2 K} {d : K} (hd : d ≠ 0)
    (hg : g * xp 7 d * g⁻¹ ∈ Up K) :
    g ∈ borel (g2Datum K) (torus (τ := .G2) K) ∨
      ∃ b ∈ borel (g2Datum K) (torus (τ := .G2) K), ∃ a : K,
        g = b * weylElement .G2 K e1 * xp 1 a := by
  have hct := g2_isCTGroupDatum K
  have hext := g2_steinbergExtras K
  obtain ⟨w, hw⟩ := exists_mem_bruhatCell hct hext g
  obtain ⟨b, hb, u, hu, rfl⟩ := exists_eq_mul_nrep_mul hct hext hw
  have huU : u ∈ Ug K :=
    (posUnipotent_eq_Ug (K := K)).le (inversionUnipotent_le_posUnipotent w hu)
  obtain ⟨t, htl, hrt⟩ := weylAction_long K w 7 (by simp [longPos])
  have ht12 : t < 12 := by
    simp only [longPos, Finset.mem_insert, Finset.mem_singleton] at htl
    omega
  have hr7 : rt 7 ∈ (g2Datum K).roots := mem_g2_roots.2 (isRoot_rt (by norm_num))
  have hxt : nrep hct w * xp 7 d * (nrep hct w)⁻¹ ∈ Xp K t := by
    have h := (actsAs_nrep hct w).conj_mem hr7 (xp_mem_Xp 7 (by norm_num) d)
    rw [hrt] at h
    exact h
  obtain ⟨c', hc'⟩ := (mem_Xp_iff ht12 _).1 hxt
  have hc'0 : c' ≠ 0 := by
    intro h
    rw [h, xp_zero] at hc'
    have h1 : xp 7 d = 1 := by
      calc xp 7 d = (nrep hct w)⁻¹ * (nrep hct w * xp 7 d * (nrep hct w)⁻¹) * nrep hct w := by
            group
        _ = (nrep hct w)⁻¹ * 1 * nrep hct w := by rw [← hc']
        _ = 1 := by group
    exact xp_ne_one (by norm_num) hd h1
  have hconj : (b * nrep hct w * u) * xp 7 d * (b * nrep hct w * u)⁻¹ = b * xp t c' * b⁻¹ := by
    rw [hc', show (b * nrep hct w * u) * xp 7 d * (b * nrep hct w * u)⁻¹ =
        b * (nrep hct w * (u * xp 7 d * u⁻¹) * (nrep hct w)⁻¹) * b⁻¹ by group,
      show u * xp 7 d * u⁻¹ = xp 7 d by rw [Ug_comm_xp7 huU]; group]
  rw [hconj] at hg
  have hbTU : ∃ t0 ∈ Tg K, ∃ u0 ∈ Ug K, b = t0 * u0 := by
    have hb' : b ∈ (borel (g2Datum K) (torus (τ := .G2) K) : Set (adjointGroup .G2 K)) := hb
    rw [coe_borel hct, Set.mem_mul] at hb'
    obtain ⟨t0, ht0, u0, hu0, rfl⟩ := hb'
    exact ⟨t0, ht0, u0, (posUnipotent_eq_Ug (K := K)).le hu0, rfl⟩
  have hB : xp t c' ∈ borel (g2Datum K) (torus (τ := .G2) K) := by
    have h1 : b * xp t c' * b⁻¹ ∈ borel (g2Datum K) (torus (τ := .G2) K) :=
      posUnipotent_le_borel ((posUnipotent_eq_Ug (K := K)).ge (Up_le_Ug hg))
    have := mul_mem (mul_mem (inv_mem hb) h1) hb
    rwa [show b⁻¹ * (b * xp t c' * b⁻¹) * b = xp t c' by group] at this
  have ht7 : t = 7 := by
    simp only [longPos, Finset.mem_insert, Finset.mem_singleton] at htl
    rcases htl with rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      apply hc'0
      obtain ⟨t0, ht0, u0, hu0, rfl⟩ := hbTU
      obtain ⟨c, rfl⟩ := exists_ordProd hu0
      have h1 : t0 * (ordProd c * xp 0 c' * (ordProd c)⁻¹) * t0⁻¹ ∈ Up K := by
        rwa [show t0 * (ordProd c * xp 0 c' * (ordProd c)⁻¹) * t0⁻¹ =
          t0 * ordProd c * xp 0 c' * (t0 * ordProd c)⁻¹ by group]
      exact eq_zero_of_conj_x0 c c' ((Tg_conj_Up_iff ht0).2 h1)
    · exfalso
      exact hc'0 (neg_root_not_mem_borel (by norm_num) (by decide +kernel) hB)
    · exfalso
      apply hc'0
      obtain ⟨t0, ht0, u0, hu0, rfl⟩ := hbTU
      obtain ⟨c, rfl⟩ := exists_ordProd hu0
      have h1 : t0 * (ordProd c * xp 3 c' * (ordProd c)⁻¹) * t0⁻¹ ∈ Up K := by
        rwa [show t0 * (ordProd c * xp 3 c' * (ordProd c)⁻¹) * t0⁻¹ =
          t0 * ordProd c * xp 3 c' * (t0 * ordProd c)⁻¹ by group]
      exact eq_zero_of_conj_x3 c c' ((Tg_conj_Up_iff ht0).2 h1)
    · exfalso
      exact hc'0 (neg_root_not_mem_borel (by norm_num) (by decide +kernel) hB)
    · rfl
    · exfalso
      exact hc'0 (neg_root_not_mem_borel (by norm_num) (by decide +kernel) hB)
  subst ht7
  rcases weyl_stab_h w hrt with rfl | rfl
  · left
    rw [nrep_one hct, mul_one]
    exact mul_mem hb (posUnipotent_le_borel ((posUnipotent_eq_Ug (K := K)).ge huU))
  · right
    obtain ⟨a, rfl⟩ := (mem_Xp_iff (by norm_num) u).1 (inversionUnipotent_simple_le hu)
    exact ⟨b, hb, a, by rw [nrep_simple hct]⟩

end CFSG.RankThree.PartOne.SEITZ6
