module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonCfg2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case2Red

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16c11_v1_exists_mul_of_sup_eq_top {W : Type*} [CommGroup W] {Y Z : Subgroup W}
    (h : Y ⊔ Z = ⊤) (w : W) : ∃ y ∈ Y, ∃ z ∈ Z, w = y * z := by
  have hw : w ∈ Y ⊔ Z := h ▸ Subgroup.mem_top w
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.1 hw
  exact ⟨y, hy, z, hz, hyz.symm⟩

private theorem s16c11_v1_eq_bot_of_invariant_complement {W : Type*} [CommGroup W]
    {H : Subgroup (MulAut W)} {Y Z : Subgroup W}
    (hZ : Z ≤ fixV H) (hcomm : commV H = ⊤) (hY : ∀ h ∈ H, ∀ y ∈ Y, h y ∈ Y)
    (hsup : ∀ w, ∃ y ∈ Y, ∃ z ∈ Z, w = y * z) (hinf : Y ⊓ Z = ⊥) : Z = ⊥ := by
  have hYtop : Y = ⊤ := by
    rw [eq_top_iff, ← hcomm]
    refine (closure_le _).2 ?_
    rintro _ ⟨h, hh, w, rfl⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := hsup w
    have e : h (y * z) * (y * z)⁻¹ = h y * y⁻¹ := by
      rw [map_mul, hZ hz h hh]
      group
    rw [e]
    exact mul_mem (hY h hh y hy) (inv_mem hy)
  rwa [hYtop, top_inf_eq] at hinf

private theorem s16c11_v1_kappa_ker (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (w : Vtil V₀ V hV)
    (hw : s15T7Kappa V₀ (v1Sub D.M V₀ V hV L) V hV (s15_Infra_le_v1Sub D.M V₀ V hV L) w = 1) :
    w ∈ fixV (barSub V₀ V hV L) := by
  obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV w
  have hx : x.val ∈ v1Sub D.M V₀ V hV L := by
    have h1 : mkTil (v1Sub D.M V₀ V hV L) V hV x = 1 := hw
    exact (QuotientGroup.eq_one_iff (N := modNull (v1Sub D.M V₀ V hV L) V hV) x).1 h1
  have hmem : mkTil V₀ V hV x ∈ imgTil V₀ V hV (v1Sub D.M V₀ V hV L) :=
    (mem_imgTil V₀ V hV _ _).2 ⟨x, hx, rfl⟩
  have hfix := s15_Core_imgTil_v1Sub_le_fixV h (m := (1 : G)) D.M.one_mem
  simpa only [conjSubgroup_one] using hfix hmem

private theorem s16c11_v1_perm_orbit :
    ∀ σ : Equiv.Perm (Fin 3), σ ≠ 1 → σ ^ 3 = 1 →
      ∀ i j : Fin 3, j = i ∨ j = σ i ∨ j = σ (σ i) := by
  decide

private theorem s16c11_v1_model_fpf {W : Type} [CommGroup W] {X K : Subgroup (MulAut W)}
    {J₀ : Subgroup W} (hsq : ∀ w : W, w ^ 2 = 1) (hM : S16C11Model X K J₀)
    {κ : MulAut W} (hκK : κ ∈ K) (hκne : κ ≠ 1) (hκ3 : κ ^ 3 = 1) :
    ∀ u : W, κ u = u → u = 1 := by
  intro u hu
  obtain ⟨s, ψ, hs, -⟩ := hM
  have hκ'3 : (⟨κ, hκK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hκ3)
  have hσκ_ne : s ⟨κ, hκK⟩ ≠ 1 := fun h =>
    hκne (by
      have h1 : (⟨κ, hκK⟩ : ↥K) = 1 := s.injective (by rw [h, map_one])
      have h2 := congrArg (fun x : ↥K => (x : MulAut W)) h1
      simpa using h2)
  have hσκ3 : (s ⟨κ, hκK⟩) ^ 3 = 1 := by rw [← map_pow, hκ'3, map_one]
  have hτ_ne : (s ⟨κ, hκK⟩)⁻¹ ≠ 1 := by
    intro h
    exact hσκ_ne (by rw [← inv_inv (s ⟨κ, hκK⟩), h, inv_one])
  have hτ3 : ((s ⟨κ, hκK⟩)⁻¹) ^ 3 = 1 := by rw [inv_pow, hσκ3, inv_one]
  have hfix : ∀ i : Fin 3, (ψ u).1 i = (ψ u).1 (((s ⟨κ, hκK⟩)⁻¹) i) := by
    intro i
    have h := hs ⟨κ, hκK⟩ u i
    rwa [hu] at h
  have hall : ∀ i j : Fin 3, (ψ u).1 i = (ψ u).1 j := by
    intro i j
    rcases s16c11_v1_perm_orbit ((s ⟨κ, hκK⟩)⁻¹) hτ_ne hτ3 i j with h | h | h
    · rw [h]
    · rw [h, hfix i]
    · rw [h, ← hfix (((s ⟨κ, hκK⟩)⁻¹) i), ← hfix i]
  have htriple : (ψ u).1 0 * (ψ u).1 1 * (ψ u).1 2 = 1 :=
    (s16c2m_mem_Triples_iff (ψ u).1).1 (ψ u).2
  have hsq0 : (ψ u).1 0 ^ 2 = 1 := by
    apply Subtype.ext
    simpa using hsq (((ψ u).1 0 : ↥J₀) : W)
  have h0 : (ψ u).1 0 = 1 := by
    have h1 : (ψ u).1 0 * (ψ u).1 0 * (ψ u).1 0 = 1 := by
      rwa [hall 1 0, hall 2 0] at htriple
    have h3 : (ψ u).1 0 ^ 3 = 1 := by
      rw [pow_succ, pow_two]
      exact h1
    have h2 : (ψ u).1 0 = (ψ u).1 0 ^ 3 := by rw [pow_succ, hsq0, one_mul]
    rw [h2, h3]
  have hψu : ψ u = 1 := by
    apply Subtype.ext
    funext i
    show (ψ u).1 i = 1
    rw [hall i 0, h0]
  exact ψ.injective (by rw [hψu, map_one])

theorem s16c11_v1_z_fpf (D : Data G) (hin : In10 D) (h1217 : R1217 D)
    {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV)
    (hs : s15 D.M ⊥ V hV L = 1)
    {P : s16e_two_NatPred (vStar D.M ⊥ V hV L)} (hF : s16e_two_Fam D ⊥ V L hV P)
    (hK : IsSym ↥(kBar D.M ⊥ V hV L) 3) :
    ∀ k ∈ kBar D.M ⊥ V hV L, orderOf k = 3 → ∀ w : Vtil ⊥ V hV, k w = w → w = 1 := by
  have hcomm : commV (lBar ⊥ V hV L) = ⊤ := by
    rw [commV_eq_commSub]
    simpa [wTil, lBar] using wTil_eq_top_of_case163_2 hc.conc hs
  obtain ⟨J₀, J₁, hN₀, hN₁, F⟩ :=
    s16e_two_cfg2 D hin.hx hin.h61 hin.h127 hin.h1214 hV hc.setting hc.ne_bot hs hF
  have hE₀ := hF.natFacts.endUnits J₀ hN₀
  have hE₁ := hF.natFacts.endUnits J₁ hN₁
  obtain ⟨ρ, hρL, hρκ⟩ := s16e_two_kappa_equiv D h1217 hc.setting.hyp151 hV
  have hKmap := s16e_two_map_cent ρ (s16e_two_lBar_le D hc.setting.hyp151 hV)
    (s16e_two_lStar_le D hc.setting.hyp151 hV) hρL
  have hKmap' :
      ((s16e_two_cent (Mbar D.M (v1Sub D.M ⊥ V hV L) V hV) (lStar D.M ⊥ V hV L)).subgroupOf
          (Mbar D.M (v1Sub D.M ⊥ V hV L) V hV)).map ρ.symm.toMonoidHom =
        (kBar D.M ⊥ V hV L).subgroupOf (Mbar D.M ⊥ V hV) := by
    unfold s16e_two_cent
    rw [← hKmap, Subgroup.map_map]
    have hcomp : ρ.symm.toMonoidHom.comp ρ.toMonoidHom = MonoidHom.id ↥(Mbar D.M ⊥ V hV) := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id]
    unfold kBar
    rfl
  have hKstar : IsSym ↥(s16e_two_cent (Mbar D.M (v1Sub D.M ⊥ V hV L) V hV)
      (lStar D.M ⊥ V hV L)) 3 :=
    s16e_two_isSym_transport ρ.symm inf_le_left
      (inf_le_left : kBar D.M ⊥ V hV L ≤ Mbar D.M ⊥ V hV) hKmap' hK
  have hM : S16C11Model (Mbar D.M (v1Sub D.M ⊥ V hV L) V hV)
      (s16e_two_cent (Mbar D.M (v1Sub D.M ⊥ V hV L) V hV) (lStar D.M ⊥ V hV L)) J₀ :=
    s16c11_model_of_cfg2 F inf_le_left
      (fun k hk l hl => (Subgroup.mem_centralizer_iff.1 hk.2 l hl).symm) hKstar hE₀ hE₁
  intro k hk_bar hk3
  have hk_ne : k ≠ 1 := by
    rintro rfl
    simp at hk3
  have hk3pow : k ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [hk3])
  have hkM : k ∈ Mbar D.M ⊥ V hV := hk_bar.1
  let kappa : Vtil ⊥ V hV →* vStar D.M ⊥ V hV L :=
    s15T7Kappa ⊥ (v1Sub D.M ⊥ V hV L) V hV (s15_Infra_le_v1Sub D.M ⊥ V hV L)
  have hκ_equiv : ∀ (g : ↥(Mbar D.M ⊥ V hV)) (v : Vtil ⊥ V hV),
      kappa ((g : MulAut (Vtil ⊥ V hV)) v) =
        (ρ g : MulAut (vStar D.M ⊥ V hV L)) (kappa v) := hρκ
  have hC : ∀ x : Vtil ⊥ V hV, k x = x → x ∈ fixV (lBar ⊥ V hV L) := by
    intro x hx
    have hρk_ne : (ρ ⟨k, hkM⟩ : ↥(Mbar D.M (v1Sub D.M ⊥ V hV L) V hV)) ≠ 1 := fun h =>
      hk_ne (by
        have h1 : (⟨k, hkM⟩ : ↥(Mbar D.M ⊥ V hV)) = 1 := ρ.injective (by simpa using h)
        have h2 := congrArg (fun x : ↥(Mbar D.M ⊥ V hV) =>
          (x : MulAut (Vtil ⊥ V hV))) h1
        simpa using h2)
    have hκ_ne : ((ρ ⟨k, hkM⟩ : ↥(Mbar D.M (v1Sub D.M ⊥ V hV L) V hV)) :
        MulAut (vStar D.M ⊥ V hV L)) ≠ 1 := fun h => hρk_ne (Subtype.ext h)
    have hsub3 : (⟨k, hkM⟩ : ↥(Mbar D.M ⊥ V hV)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hk3pow)
    have hρk3 : (ρ ⟨k, hkM⟩ : ↥(Mbar D.M (v1Sub D.M ⊥ V hV L) V hV)) ^ 3 = 1 := by
      rw [← map_pow, hsub3, map_one]
    have hκ3 : ((ρ ⟨k, hkM⟩ : ↥(Mbar D.M (v1Sub D.M ⊥ V hV L) V hV)) :
        MulAut (vStar D.M ⊥ V hV L)) ^ 3 = 1 := by
      have hcoe := congrArg (fun x : ↥(Mbar D.M (v1Sub D.M ⊥ V hV L) V hV) =>
        (x : MulAut (vStar D.M ⊥ V hV L))) hρk3
      simpa using hcoe
    have hρkK : ((ρ ⟨k, hkM⟩ : ↥(Mbar D.M (v1Sub D.M ⊥ V hV L) V hV)) :
        MulAut (vStar D.M ⊥ V hV L)) ∈
        s16e_two_cent (Mbar D.M (v1Sub D.M ⊥ V hV L) V hV) (lStar D.M ⊥ V hV L) := by
      have hmem : ρ ⟨k, hkM⟩ ∈
          (s16e_two_cent (Mbar D.M (v1Sub D.M ⊥ V hV L) V hV)
            (lStar D.M ⊥ V hV L)).subgroupOf (Mbar D.M (v1Sub D.M ⊥ V hV L) V hV) := by
        unfold s16e_two_cent
        rw [← hKmap]
        exact Subgroup.mem_map_of_mem ρ.toMonoidHom (Subgroup.mem_subgroupOf.2 hk_bar)
      exact hmem
    have hfixκ : ((ρ ⟨k, hkM⟩ : ↥(Mbar D.M (v1Sub D.M ⊥ V hV L) V hV)) :
        MulAut (vStar D.M ⊥ V hV L)) (kappa x) = kappa x := by
      rw [← hκ_equiv ⟨k, hkM⟩ x]
      change kappa (k x) = kappa x
      rw [hx]
    have hκx : kappa x = 1 :=
      s16c11_v1_model_fpf F.sq hM hρkK hκ_ne hκ3 (kappa x) hfixκ
    exact s16c11_v1_kappa_ker D hc.setting.hyp151 hV x hκx
  intro w hw
  have hZle : fixV (Subgroup.zpowers k) ≤ fixV (lBar ⊥ V hV L) := by
    intro x hx
    exact hC x ((CFSG.Quasithin.mem_fixV_zpowers_iff).1 hx)
  have hodd : Odd (Nat.card (Subgroup.zpowers k)) := by
    rw [Nat.card_zpowers, hk3]
    norm_num
  have hdec := CFSG.Quasithin.B1.coprime_decomp (V := Vtil ⊥ V hV)
    (s15_Infra_vtil_sq_eq_one ⊥ V hV) (Y := Subgroup.zpowers k) hodd (M := ⊤)
    (fun _ _ _ _ => Subgroup.mem_top _)
  simp only [top_inf_eq] at hdec
  have hY : ∀ h ∈ lBar ⊥ V hV L, ∀ y ∈ commSub ⊤ (Subgroup.zpowers k),
      h y ∈ commSub ⊤ (Subgroup.zpowers k) := by
    intro g hg y hy
    have hgk : g * k = k * g := Subgroup.mem_centralizer_iff.1 hk_bar.2 g hg
    have hconj_k : (MulAut.conj g) k = k := by
      rw [MulAut.conj_apply, hgk, mul_assoc, mul_inv_cancel, mul_one]
    have hconj_g : (Subgroup.zpowers k).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers k := by
      rw [MonoidHom.map_zpowers]
      change Subgroup.zpowers ((MulAut.conj g) k) = Subgroup.zpowers k
      rw [hconj_k]
    have h2 := CFSG.Quasithin.Asc81c.commSub_map_conj (Subgroup.zpowers k) g
    rw [hconj_g] at h2
    rw [h2]
    exact Subgroup.mem_map_of_mem g.toMonoidHom hy
  have hsupY : (commSub ⊤ (Subgroup.zpowers k)) ⊔ fixV (Subgroup.zpowers k) = ⊤ := by
    rw [sup_comm]
    exact hdec.1
  have hsup : ∀ w : Vtil ⊥ V hV, ∃ y ∈ commSub ⊤ (Subgroup.zpowers k),
      ∃ z ∈ fixV (Subgroup.zpowers k), w = y * z :=
    s16c11_v1_exists_mul_of_sup_eq_top hsupY
  have hinf : (commSub ⊤ (Subgroup.zpowers k)) ⊓ fixV (Subgroup.zpowers k) = ⊥ := by
    rw [inf_comm]
    exact hdec.2
  have hZbot : fixV (Subgroup.zpowers k) = ⊥ :=
    s16c11_v1_eq_bot_of_invariant_complement hZle hcomm hY hsup hinf
  have hwZ : w ∈ fixV (Subgroup.zpowers k) := (CFSG.Quasithin.mem_fixV_zpowers_iff).2 hw
  rw [hZbot, Subgroup.mem_bot] at hwZ
  exact hwZ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
