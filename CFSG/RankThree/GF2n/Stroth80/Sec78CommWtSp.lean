module

public import CFSG.RankThree.GF2n.Stroth80.Sec83Upper
public import CFSG.RankThree.GF2n.Stroth80.Sec78CentreStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open CFSG.ClassicalGroups.F2Fixed (fixedSub mem_fixedSub)
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8ctr_comm_W_le_Z (h34 : Stroth34Statement) (h53 : Stroth53Statement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} {m : ℕ} {K : Type} [Field K] [Finite K]
    {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K} {u u' : Fin m ⊕ Fin m → K}
    (hs : Sec5Hyp hc n t) (hr : Sec7A hc t r) (hpts : Sec8Pts hc t r m K φ u u')
    (hM6 : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ⁅ρ, w⁆ ∈ Sec8W1 M Q Z B t r)
    {s : G} (hsR : s ∈ Rt M (LB M Q B) t) (hsc : ∀ ρ ∈ Rt M (LB M Q B) t, ⁅s, ρ⁆ ∈ Q) :
    ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅s, w⁆ ∈ Z := by
  classical
  haveI := hpts.charP
  have h8 : Sec8Hyp hc n t := ⟨hs, m, hpts.two_le, hpts.spMNat⟩
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.mem
  have hL'R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t :=
    hc.LB_conj_le_Rt_of_mem hs.mem hrR
  have hinv := sec8InvStatement_holds G M Q Z B hc n t h8 r hr
  have hcd := h53.2.2.1 G M Q Z B hc n t hs hpts.spNat r hrR hr.plane (conjSubgroup r B)
    (LB M Q B) (LB M Q (conjSubgroup r B)) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r)
    (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl rfl
  have hd := h53.2.2.2.1 G M Q Z B hc n t hs hpts.spNat r hrR hr.plane (conjSubgroup r B)
    (hc.CN t) (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r)
    (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl rfl
  have hsN : s ∈ hc.CN t := by
    obtain ⟨Z0, hZ0⟩ := exists_isCentrePre (hc.Q_le_Rt hs.mem)
    exact sec8_Z0_le_CN hc h8 hZ0 ((hZ0 s).mpr ⟨hsR, hsc⟩)
  have hZQ : Z ≤ Q := hc.hyp.Z_normal.1
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hnormQ : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ x ∈ Q, ρ * x * ρ⁻¹ ∈ Q := fun ρ hρ x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hRM hρ)) x).mp hx
  have hnormZ : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ x ∈ Z, ρ * x * ρ⁻¹ ∈ Z := fun ρ hρ x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (hRM hρ)) x).mp hx
  have hcommQ : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ x ∈ Q, ⁅ρ, x⁆ ∈ Q := fun ρ hρ x hx => by
    rw [commutatorElement_def]
    exact Q.mul_mem (hnormQ ρ hρ x hx) (Q.inv_mem hx)
  have hSec : SecHyp (Rt M (LB M Q B) t) Q Z :=
    ⟨hZQ, fun x hx y hy => hc.hyp.toHyp79.comm_mem_V hx hy,
      fun x hx => hc.hyp.toHyp79.sq_mem_V hx, hnormQ, hnormZ⟩
  obtain ⟨Md, _, _, κ, hκ⟩ := exists_sectionModule hSec
  haveI : Finite Md := hκ.finite
  obtain ⟨ε, hε1, hεR⟩ := exists_comm_endo hc hRM hκ (hRM hsR) (fun ρ hρ => by
    rw [← commutatorElement_inv]
    exact Q.inv_mem (hsc ρ⁻¹ ((Rt M (LB M Q B) t).inv_mem hρ)))
  have hV1ε : ∀ a ∈ secSub κ (Sec8V1 M Q Z B t r), ε a = 0 := by
    intro a ha
    obtain ⟨x, hxV₁, hxa⟩ := mem_secSub.mp ha
    have hxa' : Multiplicative.toAdd (κ x) = a := by rw [hxa]; rfl
    rw [← hxa', hε1 x]
    have hZ : ⁅(x : G), s⁆ ∈ Z := by
      rw [← commutatorElement_inv]
      exact Z.inv_mem (hd.1 s hsN x hxV₁)
    have : κ ⟨⁅(x : G), s⁆, hc.comm_mem_Q (hRM hsR) x.2⟩ = 1 := (hκ.ker _).mpr hZ
    rw [this]
    rfl
  obtain ⟨hVA1, hA1W, hVA2, hA2W, hsup, -, -, -, hA1c, hA2c⟩ := hcd
  have hW₁Q : Sec8W1 M Q Z B t r ≤ Q := inf_le_left
  have hV₁Q : Sec8V1 M Q Z B t r ≤ Q := inf_le_left.trans (sup_le inf_le_left hVQ)
  have hA1 : ∀ a ∈ secSub κ (QB B ⊓ Sec8W1 M Q Z B t r ⊔ Sec8V1 M Q Z B t r),
      ∀ l ∈ (LB M Q B).subgroupOf (Rt M (LB M Q B) t),
      l • a - a ∈ secSub κ (Sec8V1 M Q Z B t r) := by
    intro a ha l hl
    obtain ⟨x, hxA, hxa⟩ := mem_secSub.mp ha
    have hxa' : Multiplicative.toAdd (κ x) = a := by rw [hxa]; rfl
    have hlx : ⁅(l : G), (x : G)⁆ ∈ Sec8V1 M Q Z B t r :=
      (hA1c x (hA1W hxA)).mp hxA l (Subgroup.mem_subgroupOf.mp hl)
    rw [← hxa', smul_toAdd_sub_eq hκ hnormQ l x (hcommQ l l.2 x x.2)]
    exact mem_secSub.mpr ⟨⟨⁅(l : G), (x : G)⁆, hcommQ l l.2 x x.2⟩, hlx, rfl⟩
  have hA2 : ∀ a ∈ secSub κ (QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r ⊔ Sec8V1 M Q Z B t r),
      ∀ l ∈ (LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t),
      l • a - a ∈ secSub κ (Sec8V1 M Q Z B t r) := by
    intro a ha l hl
    obtain ⟨x, hxA, hxa⟩ := mem_secSub.mp ha
    have hxa' : Multiplicative.toAdd (κ x) = a := by rw [hxa]; rfl
    have hlx : ⁅(l : G), (x : G)⁆ ∈ Sec8V1 M Q Z B t r :=
      (hA2c x (hA2W hxA)).mp hxA l (Subgroup.mem_subgroupOf.mp hl)
    rw [← hxa', smul_toAdd_sub_eq hκ hnormQ l x (hcommQ l l.2 x x.2)]
    exact mem_secSub.mpr ⟨⟨⁅(l : G), (x : G)⁆, hcommQ l l.2 x x.2⟩, hlx, rfl⟩
  have hW1 : secSub κ (Sec8W1 M Q Z B t r) =
      secSub κ (QB B ⊓ Sec8W1 M Q Z B t r ⊔ Sec8V1 M Q Z B t r) ⊔
        secSub κ (QB (conjSubgroup r B) ⊓ Sec8W1 M Q Z B t r ⊔ Sec8V1 M Q Z B t r) := by
    rw [← secSub_sup (hA1W.trans hW₁Q) (hA2W.trans hW₁Q), hsup]
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have h35B := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  have h35C := (stroth_3_5 h34 hcC hs.width hs.n_gt (hc.noA2_conj hs.noA2 hrM)
    (hs.gen.conj_of_mem hrM)).2.1
  have hF₁ : ∀ b : Md, (∀ l ∈ (LB M Q B).subgroupOf (Rt M (LB M Q B) t), l • b = b) →
      b ∈ secSub κ (B ⊔ Z) := by
    intro b hb
    have hmem : b ∈ fixedSub Md (((LB M Q B).subgroupOf (Rt M (LB M Q B) t) :
        Subgroup ↥(Rt M (LB M Q B) t)) : Set ↥(Rt M (LB M Q B) t)) :=
      mem_fixedSub.mpr fun x hx => hb x hx
    obtain ⟨x, hxb, hxc⟩ := (mem_fixedSub_iff hnormQ hκ hLR).mp hmem
    have hx : (x : G) ∈ CQt Q Z (LB M Q B) := ⟨x.2, fun l hl => hxc l hl⟩
    rw [h35B] at hx
    exact mem_secSub.mpr ⟨x, hx, hxb⟩
  have hF₂ : ∀ b : Md, (∀ l ∈ (LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t),
      l • b = b) → b ∈ secSub κ (conjSubgroup r B ⊔ Z) := by
    intro b hb
    have hmem : b ∈ fixedSub Md (((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t) :
        Subgroup ↥(Rt M (LB M Q B) t)) : Set ↥(Rt M (LB M Q B) t)) :=
      mem_fixedSub.mpr fun x hx => hb x hx
    obtain ⟨x, hxb, hxc⟩ := (mem_fixedSub_iff hnormQ hκ hL'R).mp hmem
    have hx : (x : G) ∈ CQt Q Z (LB M Q (conjSubgroup r B)) := ⟨x.2, fun l hl => hxc l hl⟩
    rw [h35C] at hx
    exact mem_secSub.mpr ⟨x, hx, hxb⟩
  have hq2 : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have hBZV : B ⊔ Z ≤ Vt M (LB M Q B) B Z t := sup_le (hc.B_le_Vt hs.mem) sec39_Z_le_Vt
  have hCZV : conjSubgroup r B ⊔ Z ≤ Vt M (LB M Q B) B Z t := hc.conj_Rt_le_Vt hs.mem hrR
  have hBcard : Nat.card B = Nat.card Z := by
    obtain ⟨g, hg⟩ := hc.conj
    rw [hg, card_conjSubgroup]
  have hCcard : Nat.card (conjSubgroup r B) = Nat.card Z := by
    rw [card_conjSubgroup, hBcard]
  have hcardF₁ : Nat.card ↥(secSub κ (B ⊔ Z)) ≤ Nat.card Z := by
    have h1 := natCard_secSub_mul hZQ hκ (le_sup_right : Z ≤ B ⊔ Z) (sup_le hc.le hZQ)
    rw [hc.card_sup_Z, hBcard] at h1
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h1).le
  have hcardF₂ : Nat.card ↥(secSub κ (conjSubgroup r B ⊔ Z)) ≤ Nat.card Z := by
    have h1 := natCard_secSub_mul hZQ hκ (le_sup_right : Z ≤ conjSubgroup r B ⊔ Z)
      (sup_le hcC.le hZQ)
    rw [hcC.card_sup_Z, hCcard] at h1
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h1).le
  have hirrG : ∀ U : Subgroup G, Z ≤ U → U ≤ Vt M (LB M Q B) B Z t →
      (∀ ρ ∈ Rt M (LB M Q B) t, ∀ u ∈ U, ρ * u * ρ⁻¹ ∈ U) → U = Z ∨ U = Vt M (LB M Q B) B Z t :=
    fun U hZU hUV hRU => hpts.naturalRep.eq_or_eq_of_invariant natIrred_statedSp
      addCommutantScalar_statedSp hZU hUV hRU
  have hirr := secSub_irred_of_irred hκ sec39_Z_le_Vt hVQ hnormQ hirrG
  have hcardV : Nat.card ↥(secSub κ (Vt M (LB M Q B) B Z t)) = Nat.card Z ^ (2 * m) := by
    have h1 := natCard_secSub_mul hZQ hκ sec39_Z_le_Vt hVQ
    rw [hpts.card_V, pow_succ] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hm2 := hpts.two_le
  have hqq : Nat.card Z * Nat.card Z < Nat.card ↥(secSub κ (Vt M (LB M Q B) B Z t)) := by
    rw [hcardV, ← pow_two]
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  have hq : Nat.card Z < Nat.card ↥(secSub κ (Vt M (LB M Q B) B Z t)) := by
    rw [hcardV]
    calc Nat.card Z = Nat.card Z ^ 1 := (pow_one _).symm
      _ < Nat.card Z ^ (2 * m) := Nat.pow_lt_pow_right (by omega) (by omega)
  have hinvW1 : ∀ z : ↥(Rt M (LB M Q B) t), ∀ a ∈ secSub κ (Sec8W1 M Q Z B t r),
      z • a ∈ secSub κ (Sec8W1 M Q Z B t r) := by
    intro z a ha
    have h1 := secSub_conjSubgroup hnormQ hκ z (Sec8W1 M Q Z B t r)
    rw [(hinv z z.2).2] at h1
    have : z • a ∈ (secSub κ (Sec8W1 M Q Z B t r)).map (DistribSMul.toAddMonoidHom Md z) :=
      ⟨a, ha, rfl⟩
    rwa [← h1] at this
  have hinvW : ∀ z : ↥(Rt M (LB M Q B) t), ∀ a ∈ secSub κ (Wt Q (Vt M (LB M Q B) B Z t)),
      z • a ∈ secSub κ (Wt Q (Vt M (LB M Q B) B Z t)) := by
    intro z a ha
    have h0 : conjSubgroup (z : G) (Wt Q (Vt M (LB M Q B) B Z t)) =
        Wt Q (Vt M (LB M Q B) B Z t) :=
      sec8_conjSubgroup_eq_of_mem_normalizer (sec8_Wt_mem_normalizer
        (hc.hyp.Q_normal.2 (hRM z.2)) (hc.Rt_normalizes_Vt hs.mem z.2))
    have h1 := secSub_conjSubgroup hnormQ hκ z (Wt Q (Vt M (LB M Q B) B Z t))
    rw [h0] at h1
    have : z • a ∈ (secSub κ (Wt Q (Vt M (LB M Q B) B Z t))).map
        (DistribSMul.toAddMonoidHom Md z) := ⟨a, ha, rfl⟩
    rwa [← h1] at this
  have hε0W1 : ∀ a ∈ secSub κ (Sec8W1 M Q Z B t r), ε a = 0 :=
    eps_kills_sW1 ε hεR hV1ε hA1 hA2 hW1 hF₁ hF₂ (secSub_mono hBZV) (secSub_mono hCZV)
      hcardF₁ hcardF₂ hirr hqq hinvW1
  have hW' : ∀ a ∈ secSub κ (Wt Q (Vt M (LB M Q B) B Z t)),
      ∀ l ∈ (LB M Q B).subgroupOf (Rt M (LB M Q B) t),
      l • a - a ∈ secSub κ (Sec8W1 M Q Z B t r) := by
    intro a ha l hl
    obtain ⟨x, hxW, hxa⟩ := mem_secSub.mp ha
    have hxa' : Multiplicative.toAdd (κ x) = a := by rw [hxa]; rfl
    rw [← hxa', smul_toAdd_sub_eq hκ hnormQ l x (hcommQ l l.2 x x.2)]
    exact mem_secSub.mpr ⟨⟨⁅(l : G), (x : G)⁆, hcommQ l l.2 x x.2⟩, hM6 l l.2 x hxW, rfl⟩
  have hε0W : ∀ a ∈ secSub κ (Wt Q (Vt M (LB M Q B) B Z t)), ε a = 0 :=
    eps_kills_sW ε hεR hε0W1 hW' hF₁ (secSub_mono hBZV) hcardF₁ hirr hq hinvW

  intro w hw
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hwQ : w ∈ Q := hWQ hw
  have h1 : ε (Multiplicative.toAdd (κ ⟨w, hwQ⟩)) = 0 :=
    hε0W _ (mem_secSub.mpr ⟨⟨w, hwQ⟩, hw, rfl⟩)
  rw [hε1 ⟨w, hwQ⟩] at h1
  have h2 : κ ⟨⁅w, s⁆, hc.comm_mem_Q (hRM hsR) hwQ⟩ = 1 := Multiplicative.toAdd.injective h1
  have h3 : ⁅w, s⁆ ∈ Z := (hκ.ker _).mp h2
  rw [← commutatorElement_inv]
  exact Z.inv_mem h3

theorem sec8CommWt_of_53 (h34 : Stroth34Statement) (h53 : Stroth53Statement)
    (hA : Sec8AExistsStatement) (hPts : Sec5NatPointsSpStatement) : Sec8CommWtStatement := by
  intro G _ _ M Q Z B hc n t hs8 Z0 hZ0 s hsZ
  have hs := hs8.toSec5
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs8
  obtain ⟨K, _, _, hK, m', hm', φ, u, u', hrange, hker, hact, huu', hL, hL'⟩ :=
    hPts G M Q Z B hc n t hs hs8.spNat r hr.mem hr.plane
  have hpts : Sec8Pts hc t r m' K φ u u' := ⟨hm', hK, hrange, hker, hact, huu', hL, hL'⟩
  exact sec8ctr_comm_W_le_Z h34 h53 hs hr hpts (sec83up_R_trivial h53 hs hr hpts)
    (hZ0.le hsZ) (fun ρ hρ => hZ0.comm_mem hsZ hρ)

end CFSG.RankThree.GF2n.Stroth80
