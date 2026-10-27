module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3AltTwoDirSum
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma218a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm13_10

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem commSub_commSub_ne_bot_of_swap {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} (hQL : QuadTrivial L) (hL : L ≠ ⊥)
    {t : MulAut W} (ht : t * t = 1) (hrk : rkIdx (fixV (Subgroup.zpowers t)) < dMinDeg ↥L) :
    commSub (commSub (⊤ : Subgroup W) L) (L.map (MulAut.conj t).toMonoidHom) ≠ ⊥ := by
  intro hbot
  set S : Subgroup W := commSub (⊤ : Subgroup W) L with hS
  set K : Subgroup (MulAut W) := L.map (MulAut.conj t).toMonoidHom with hK
  have hbot' : commSub S K = ⊥ := by simpa [hS, hK] using hbot
  have hSK : S ≤ fixV K := commSub_eq_bot_iff.mp hbot'
  have hcomp : (MulAut.conj (1 : MulAut W)).toMonoidHom = MonoidHom.id (MulAut W) := by
    ext x
    simp
  have hKK : K.map (MulAut.conj t).toMonoidHom = L := by
    have h1 := CFSG.Quasithin.B19.map_conj_map_conj L t t
    rw [ht, hcomp, Subgroup.map_id, ← hK] at h1
    exact h1
  have hfix : (fixV K).map t.toMonoidHom = fixV L :=
    (CFSG.Quasithin.fixV_map_conj_eq K t).symm.trans (by rw [hKK])
  have hinf : S ⊓ fixV (Subgroup.zpowers t) ≤ S ⊓ fixV L := by
    refine le_inf inf_le_left ?_
    intro x hx
    have hle : S.map t.toMonoidHom ≤ fixV L := by
      rw [← hfix]
      exact Subgroup.map_mono hSK
    have hmem : t x ∈ fixV L := hle (Subgroup.mem_map_of_mem t.toMonoidHom hx.1)
    have hxt : t x = x := CFSG.Quasithin.mem_fixV_zpowers_iff_apply.mp hx.2
    rwa [hxt] at hmem
  have hrank : rk S < rk ↥(S ⊓ fixV (Subgroup.zpowers t)) + dMinDeg ↥L := by
    have h1 := rk_sup_add_rk_inf S (fixV (Subgroup.zpowers t))
    have h2 : rk ↥(S ⊔ fixV (Subgroup.zpowers t)) ≤ rk W := by
      have h := rk_mono (G := W) (le_top : S ⊔ fixV (Subgroup.zpowers t) ≤ ⊤)
      rwa [rk_top] at h
    have h3 := rk_add_rkIdx (fixV (Subgroup.zpowers t))
    omega
  have hself : ∀ a ∈ L, ∀ b ∈ L, a * b * a⁻¹ ∈ L :=
    fun a ha b hb => L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)
  have hStabS : StableUnder L S := by
    rw [hS]
    exact stableUnder_commSub hself (fun x _ u _ => Subgroup.mem_top u)
  have hStabU : StableUnder L (S ⊓ fixV L) :=
    stableUnder_inf hStabS (stableUnder_fixV hself)
  have hrank' : rk S < rk ↥(S ⊓ fixV L) + dMinDeg ↥L := by
    have hmono : rk ↥(S ⊓ fixV (Subgroup.zpowers t)) ≤ rk ↥(S ⊓ fixV L) := rk_mono hinf
    omega
  have hSL : commSub S L = ⊥ :=
    hQL S hStabS ((commSub_le_of_rk_lt_dMinDeg hW inf_le_left hStabS hStabU hrank').trans
      inf_le_right)
  have hSfix : S ≤ fixV L := commSub_eq_bot_iff.mp hSL
  have hquad2 : commSub (⊤ : Subgroup W) L = ⊥ :=
    hQL ⊤ (fun x _ u _ => Subgroup.mem_top u) (by simpa [hS] using hSfix)
  have htop : fixV L = ⊤ := top_le_iff.mp (commSub_eq_bot_iff.mp hquad2)
  refine hL ?_
  rw [eq_bot_iff]
  intro l hl
  ext w
  have hw : w ∈ fixV L := by rw [htop]; exact Subgroup.mem_top w
  simpa using (mem_fixV.mp hw) l hl

theorem false_of_commute_orderOf_five {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (hrk : rk W = 8) {L K : Subgroup (MulAut W)}
    (hL : IsAlt ↥L 5) (hK : IsAlt ↥K 5) (hcomm : ∀ a ∈ L, ∀ b ∈ K, a * b = b * a)
    {c : MulAut W} (hc5 : orderOf c = 5) (hcX : ∀ x ∈ L ⊔ K, c * x = x * c) : False := by
  classical
  set Z : Subgroup (MulAut W) := Subgroup.zpowers c with hZ
  have hcardL : Nat.card ↥L = 60 := by
    obtain ⟨e⟩ := hL
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  have hcardK : Nat.card ↥K = 60 := by
    obtain ⟨e⟩ := hK
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  have hcardZ : Nat.card ↥Z = 5 := by
    rw [hZ, Nat.card_zpowers, hc5]
  have hKZ : ∀ a ∈ K, ∀ b ∈ Z, a * b = b * a := by
    intro a ha b hb
    have hc : c ∈ Subgroup.centralizer (K : Set (MulAut W)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (hcX x (Subgroup.mem_sup_right hx)).symm
    have hb' : b ∈ Subgroup.centralizer (K : Set (MulAut W)) := by
      rw [hZ] at hb
      exact Subgroup.zpowers_le.mpr hc hb
    exact Subgroup.mem_centralizer_iff.mp hb' a ha
  have hKinfZ : K ⊓ Z = ⊥ := inf_eq_bot_of_commute_isAlt_five hKZ hK
  have hcardKZ : Nat.card ↥(K ⊔ Z) = 300 := by
    rw [← Nat.card_congr (CFSG.GH74.E2.prodSupEquiv K Z hKZ hKinfZ).toEquiv,
      Nat.card_prod, hcardK, hcardZ]
  have hLsupKZ : ∀ a ∈ L, ∀ b ∈ K ⊔ Z, a * b = b * a := by
    have hKcent : K ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcomm a ha k hk
    have hZcent : Z ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
      rw [hZ]
      refine Subgroup.zpowers_le.mpr ?_
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (hcX a (Subgroup.mem_sup_left ha)).symm
    intro a ha b hb
    exact Subgroup.mem_centralizer_iff.mp (sup_le hKcent hZcent hb) a ha
  have hLinf : L ⊓ (K ⊔ Z) = ⊥ := inf_eq_bot_of_commute_isAlt_five hLsupKZ hL
  have hcardTot : Nat.card ↥(L ⊔ (K ⊔ Z)) = 18000 := by
    rw [← Nat.card_congr (CFSG.GH74.E2.prodSupEquiv L (K ⊔ Z) hLsupKZ hLinf).toEquiv,
      Nat.card_prod, hcardL, hcardKZ]
  have hcardW : Nat.card W = 2 ^ 8 := by
    have h := card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hW)
    rwa [hrk] at h
  have h2 : ∀ e : W, e * e = 1 := by
    intro e
    simpa [sq] using hW e
  have hAut := CFSG.GH74.GLS.Bg.TwoGroups.L218.card_mulAut_two h2 8 hcardW
  have hdvd : Nat.card ↥(L ⊔ (K ⊔ Z)) ∣ Nat.card (MulAut W) :=
    Subgroup.card_subgroup_dvd_card (L ⊔ (K ⊔ Z))
  rw [hcardTot] at hdvd
  have h125 : 125 ∣ Nat.card (MulAut W) := Nat.dvd_trans (by norm_num) hdvd
  rw [hAut] at h125
  norm_num [Fin.prod_univ_eight] at h125

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm13_10
