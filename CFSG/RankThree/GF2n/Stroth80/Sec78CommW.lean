module

public import CFSG.RankThree.GF2n.Stroth80.Sec78CardUt
public import CFSG.RankThree.GF2n.Stroth80.Sec7Transport
public import CFSG.RankThree.GF2n.Stroth80.Sec78CentreStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5Rt
public import CFSG.RankThree.GF2n.Stroth80.Sec83Card

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7ctr_card_Vt (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) :
    ∃ d : ℕ, 4 ≤ d ∧ Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z * Nat.card Z ^ d := by
  obtain ⟨m, hm, h | h⟩ := hs.orth
  · obtain ⟨K, fK, finK, hK, hrep⟩ := h
    have hm3 : 3 ≤ m := by
      by_contra hlt
      have : m = 2 := by omega
      subst this
      exact hs.notPlus4 ⟨K, fK, finK, hK, hrep⟩
    refine ⟨m + m, by omega, ?_⟩
    have := card_of_naturalRep hrep (sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B) (t := t)) hK
    rw [this]
    simp only [Fintype.card_sum, Fintype.card_fin]
  · obtain ⟨K, fK, finK, hK, b, c, hirr, hrep⟩ := h
    refine ⟨(m - 1) + (m - 1) + 2, by omega, ?_⟩
    have := card_of_naturalRep hrep (sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B) (t := t)) hK
    rw [this]
    simp only [Fintype.card_sum, Fintype.card_fin]
    ring_nf

theorem sec7ctr_Wt_conj_mem (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {ρ x : G}
    (hρ : ρ ∈ Rt M (LB M Q B) t) (hx : x ∈ Wt Q (Vt M (LB M Q B) B Z t)) :
    ρ * x * ρ⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
  obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
  refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ)) x).mp hxQ
  · have hv' : ρ⁻¹ * v * ρ ∈ Vt M (LB M Q B) B Z t := by
      have := (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht
        ((Rt M (LB M Q B) t).inv_mem hρ)) v).mp hv
      simpa using this
    have key := Subgroup.mem_centralizer_iff.mp hxC (ρ⁻¹ * v * ρ) hv'
    calc v * (ρ * x * ρ⁻¹) = ρ * ((ρ⁻¹ * v * ρ) * x) * ρ⁻¹ := by group
      _ = ρ * (x * (ρ⁻¹ * v * ρ)) * ρ⁻¹ := by rw [key]
      _ = ρ * x * ρ⁻¹ * v := by group

theorem sec7ctr_card_secSub_sup_le (hc : Ctx M Q Z B) {R : Subgroup G} {Md : Type}
    [AddCommGroup Md] [DistribMulAction ↥R Md] {κ : ↥Q →* Multiplicative Md}
    (hκ : IsSecMod R Q Z Md κ) {D : Subgroup G} (hDQ : D ≤ Q) (hD : Nat.card ↥D = Nat.card Z) :
    Nat.card ↥(secSub κ (D ⊔ Z)) ≤ Nat.card Z := by
  have hZQ : Z ≤ Q := hc.Z_le_Q
  have hDZ : D ⊔ Z ≤ Q := sup_le hDQ hZQ
  have h1 := natCard_secSub_mul hZQ hκ (le_sup_right : Z ≤ D ⊔ Z) hDZ
  have hnorm : D ≤ Subgroup.normalizer (Z : Set G) := fun d hd =>
    hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hDQ hd))
  have h2 := card_sup_mul_card_inf_of_le_normalizer hnorm
  rw [sup_comm] at h2
  have h3 : Nat.card ↥(D ⊔ Z) ≤ Nat.card Z * Nat.card Z := by
    have : Nat.card ↥(D ⊔ Z) ≤ Nat.card ↥(D ⊔ Z) * Nat.card ↥(Z ⊓ D : Subgroup G) :=
      Nat.le_mul_of_pos_right _ Nat.card_pos
    rw [h2, hD] at this
    exact this
  have hpos : 0 < Nat.card Z := Nat.card_pos
  rw [← h1] at h3
  have h4 : Nat.card ↥(secSub κ (D ⊔ Z)) * Nat.card Z ≤ Nat.card Z * Nat.card Z := h3
  exact Nat.le_of_mul_le_mul_right h4 hpos

theorem sec7ctr_comm_W_le_Z (h52a : Stroth52aStatement) (hirr : Sec7VtIrredStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {r : G} (hr : Sec7A hc t r)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZN : Z0 ≤ hc.CN t)
    (hZB : Z0 ≤ LB M Q B) (hZC : Z0 ≤ LB M Q (conjSubgroup r B)) {s : G} (hsZ : s ∈ Z0) :
    ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅s, w⁆ ∈ Z := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hrM : r ∈ M := hRM hr.mem
  have hZQ : Z ≤ Q := hc.Z_le_Q
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hSec := sec7ctr_secHyp hc hRM
  have hP := hSec.normP
  obtain ⟨Md, iA, iD, κ, hκ⟩ := exists_sectionModule hSec
  haveI : Finite Md := hκ.finite
  have hsR : s ∈ Rt M (LB M Q B) t := hZ0.le hsZ
  have hsM : s ∈ M := hRM hsR
  have hsc : ∀ ρ ∈ Rt M (LB M Q B) t, ⁅ρ⁻¹, s⁆ ∈ Q := fun ρ hρ => by
    rw [← commutatorElement_inv]
    exact Q.inv_mem (hZ0.comm_mem hsZ ((Rt M (LB M Q B) t).inv_mem hρ))
  obtain ⟨ε, hε, hεR⟩ := exists_comm_endo hc hRM hκ hsM hsc
  obtain ⟨hWdec, hNW⟩ := h52a G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane
    (conjSubgroup r B) (hc.CN t) (Vt M (LB M Q B) B Z t)
    (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl rfl
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hZW : Z ≤ Wt Q (Vt M (LB M Q B) B Z t) := fun z hz =>
    ⟨hZQ hz, Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (hc.hyp.toHyp79.V_central hz (hVQ hv)).symm⟩
  set sW := secSub κ (Wt Q (Vt M (LB M Q B) B Z t)) with hsW
  set T : AddSubgroup Md := sW.map ε with hT
  have hcommQ : ∀ x : ↥Q, ⁅(x : G), s⁆ ∈ Q := fun x => hc.comm_mem_Q hsM x.2
  have hTV : T ≤ secSub κ (Vt M (LB M Q B) B Z t) := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨x, hxW, hxb⟩ := mem_secSub.mp hb
    have hxb' : Multiplicative.toAdd (κ x) = b := by rw [hxb]; rfl
    rw [← hxb', hε x]
    refine (toAdd_mem_secSub_iff hκ hZV _).mpr ?_
    have h1 : ⁅s, (x : G)⁆ ∈ Vt M (LB M Q B) B Z t := hNW s (hZN hsZ) x hxW
    have e : ⁅(x : G), s⁆ = ⁅s, (x : G)⁆⁻¹ := (commutatorElement_inv s x).symm
    show ⁅(x : G), s⁆ ∈ Vt M (LB M Q B) B Z t
    rw [e]
    exact (Vt M (LB M Q B) B Z t).inv_mem h1
  have hsWinv : ∀ z : ↥(Rt M (LB M Q B) t), ∀ a ∈ sW, z • a ∈ sW := by
    intro z a ha
    obtain ⟨x, hxW, hxa⟩ := mem_secSub.mp ha
    have hxa' : Multiplicative.toAdd (κ x) = a := by rw [hxa]; rfl
    have hyQ : (z : G) * x * (z : G)⁻¹ ∈ Q := hP z z.2 x x.2
    have hact := hκ.act z x ⟨(z : G) * x * (z : G)⁻¹, hyQ⟩ rfl
    refine mem_secSub.mpr ⟨⟨(z : G) * x * (z : G)⁻¹, hyQ⟩, ?_, ?_⟩
    · exact sec7ctr_Wt_conj_mem hc ht z.2 hxW
    · rw [hact, hxa']
  have hTinv : ∀ z : ↥(Rt M (LB M Q B) t), ∀ a ∈ T, z • a ∈ T := by
    rintro z _ ⟨b, hb, rfl⟩
    exact ⟨z • b, hsWinv z b hb, hεR z b⟩
  have hBM : B ≤ Q := hc.le
  have hBcard : Nat.card ↥B = Nat.card Z := by
    obtain ⟨g, hg⟩ := hc.conj
    rw [hg, card_conjSubgroup]
  have hCcard : Nat.card ↥(conjSubgroup r B) = Nat.card Z := by
    rw [card_conjSubgroup, hBcard]
  have hCQ : conjSubgroup r B ≤ Q := (hc.conj_of_mem hrM).le
  have hsB : Nat.card ↥(secSub κ (B ⊔ Z)) ≤ Nat.card Z :=
    sec7ctr_card_secSub_sup_le hc hκ hBM hBcard
  have hsC : Nat.card ↥(secSub κ (conjSubgroup r B ⊔ Z)) ≤ Nat.card Z :=
    sec7ctr_card_secSub_sup_le hc hκ hCQ hCcard
  have hTBC : T ≤ secSub κ (B ⊔ Z) ⊔ secSub κ (conjSubgroup r B ⊔ Z) := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨x, hxW, hxb⟩ := mem_secSub.mp hb
    have hxb' : Multiplicative.toAdd (κ x) = b := by rw [hxb]; rfl
    obtain ⟨a₁, ha₁, b₁, hb₁, hxab⟩ := hWdec (x : G) hxW
    obtain ⟨ha₁B, ha₁W⟩ := Subgroup.mem_inf.mp ha₁
    obtain ⟨hb₁C, hb₁W⟩ := Subgroup.mem_inf.mp hb₁
    have ha₁Q : a₁ ∈ Q := hWQ ha₁W
    have hb₁Q : b₁ ∈ Q := hWQ hb₁W
    have hκx : κ x = κ ⟨a₁, ha₁Q⟩ * κ ⟨b₁, hb₁Q⟩ := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext hxab
    have hb_eq : b = Multiplicative.toAdd (κ ⟨a₁, ha₁Q⟩) + Multiplicative.toAdd (κ ⟨b₁, hb₁Q⟩) := by
      rw [← hxb', hκx, toAdd_mul]
    rw [hb_eq, map_add, hε ⟨a₁, ha₁Q⟩, hε ⟨b₁, hb₁Q⟩]
    refine AddSubgroup.add_mem_sup ?_ ?_
    · refine (toAdd_mem_secSub_iff hκ (le_sup_right : Z ≤ B ⊔ Z) _).mpr ?_
      have h1 : ⁅s, a₁⁆ ∈ (Z ⊔ B : Subgroup G) :=
        hc.comm_LB_inf_QB_mem_sup (hZB hsZ) ⟨ha₁Q, ha₁B⟩
      show ⁅a₁, s⁆ ∈ B ⊔ Z
      rw [← commutatorElement_inv]
      exact (B ⊔ Z).inv_mem (by rwa [sup_comm] at h1)
    · refine (toAdd_mem_secSub_iff hκ (le_sup_right : Z ≤ conjSubgroup r B ⊔ Z) _).mpr ?_
      have h1 : ⁅s, b₁⁆ ∈ (Z ⊔ conjSubgroup r B : Subgroup G) :=
        (hc.conj_of_mem hrM).comm_LB_inf_QB_mem_sup (hZC hsZ) ⟨hb₁Q, hb₁C⟩
      show ⁅b₁, s⁆ ∈ conjSubgroup r B ⊔ Z
      rw [← commutatorElement_inv]
      exact (conjSubgroup r B ⊔ Z).inv_mem (by rwa [sup_comm] at h1)
  have hTcard : Nat.card ↥T ≤ Nat.card Z * Nat.card Z := by
    have h1 : Nat.card ↥T ≤ Nat.card ↥(secSub κ (B ⊔ Z) ⊔ secSub κ (conjSubgroup r B ⊔ Z)) :=
      Nat.card_mono (Set.toFinite _) hTBC
    have h2 := card_sup_mul_card_inf_addSubgroup (secSub κ (B ⊔ Z))
      (secSub κ (conjSubgroup r B ⊔ Z))
    have h3 : Nat.card ↥(secSub κ (B ⊔ Z) ⊔ secSub κ (conjSubgroup r B ⊔ Z)) ≤
        Nat.card ↥(secSub κ (B ⊔ Z) ⊔ secSub κ (conjSubgroup r B ⊔ Z)) *
          Nat.card ↥(secSub κ (B ⊔ Z) ⊓ secSub κ (conjSubgroup r B ⊔ Z)) :=
      Nat.le_mul_of_pos_right _ Nat.card_pos
    exact h1.trans (h3.trans (h2 ▸ Nat.mul_le_mul hsB hsC))
  have hirr' : ∀ U : Subgroup G, Z ≤ U → U ≤ Vt M (LB M Q B) B Z t →
      (∀ r ∈ Rt M (LB M Q B) t, ∀ u ∈ U, r * u * r⁻¹ ∈ U) →
      U = Z ∨ U = Vt M (LB M Q B) B Z t := fun U h1 h2 h3 =>
    hirr G M Q Z B hc n t hs U h1 h2 h3
  have hVirr := secSub_irred_of_irred hκ hZV hVQ hP hirr'
  obtain ⟨d, hd4, hVcard⟩ := sec7ctr_card_Vt hc hs
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hVsec : Nat.card ↥(secSub κ (Vt M (LB M Q B) B Z t)) = Nat.card Z ^ d := by
    have h1 := natCard_secSub_mul hZQ hκ hZV hVQ
    rw [hVcard] at h1
    have hpos : 0 < Nat.card Z := Nat.card_pos
    have : Nat.card ↥(secSub κ (Vt M (LB M Q B) B Z t)) * Nat.card Z =
        Nat.card Z ^ d * Nat.card Z := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hTne : T ≠ secSub κ (Vt M (LB M Q B) B Z t) := by
    intro h
    have h1 : Nat.card ↥T = Nat.card Z ^ d := by rw [h, hVsec]
    have h2 : Nat.card Z ^ 4 ≤ Nat.card Z ^ d := Nat.pow_le_pow_right (by omega) hd4
    have h3 : Nat.card Z * Nat.card Z < Nat.card Z ^ 4 := by
      have : Nat.card Z ^ 4 = Nat.card Z * Nat.card Z * (Nat.card Z * Nat.card Z) := by ring
      rw [this]
      have hqq : 1 < Nat.card Z * Nat.card Z := by nlinarith
      exact (Nat.lt_mul_iff_one_lt_right (by omega)).mpr hqq
    omega
  have hTbot : T = ⊥ := (hVirr T hTV hTinv).resolve_right hTne
  intro w hw
  have hwQ : w ∈ Q := hWQ hw
  have h1 : ε (Multiplicative.toAdd (κ ⟨w, hwQ⟩)) ∈ T :=
    ⟨_, mem_secSub.mpr ⟨⟨w, hwQ⟩, hw, rfl⟩, rfl⟩
  rw [hTbot, AddSubgroup.mem_bot, hε ⟨w, hwQ⟩] at h1
  have h2 : κ ⟨⁅w, s⁆, hcommQ ⟨w, hwQ⟩⟩ = 1 := by
    have := congrArg Multiplicative.ofAdd h1
    simpa using this
  have h3 : ⁅w, s⁆ ∈ Z := (hκ.ker _).mp h2
  rw [← commutatorElement_inv]
  exact Z.inv_mem h3

end CFSG.RankThree.GF2n.Stroth80
