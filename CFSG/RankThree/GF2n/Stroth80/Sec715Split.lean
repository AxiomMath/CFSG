module

public import CFSG.RankThree.GF2n.Stroth80.Sec715SplitAlg
public import CFSG.RankThree.GF2n.Stroth80.Sec715SplitData
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmts

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.F2Fixed
open scoped commutatorElement

section ActLemmas

variable {G : Type} [Group G] {R P I : Subgroup G} {Mm : Type} [AddCommGroup Mm]
  [DistribMulAction ↥R Mm] {κ : ↥P →* Multiplicative Mm}

theorem sec715Spl_comm_mem_P (hsec : SecHyp R P I) (r : ↥R) (z : ↥P) :
    ⁅(r : G), (z : G)⁆ ∈ P := by
  have h1 := hsec.normP r r.2 z z.2
  have e : ⁅(r : G), (z : G)⁆ = ((r : G) * z * (r : G)⁻¹) * (z : G)⁻¹ := by
    simp only [commutatorElement_def]
  rw [e]
  exact P.mul_mem h1 (P.inv_mem z.2)

theorem sec715Spl_comm_eq (hsec : SecHyp R P I) (hκ : IsSecMod R P I Mm κ) (r : ↥R) (z c : ↥P)
    (hc : (c : G) = ⁅(r : G), (z : G)⁆) :
    r • Multiplicative.toAdd (κ z) - Multiplicative.toAdd (κ z) =
      Multiplicative.toAdd (κ c) := by
  have hy : (r : G) * z * (r : G)⁻¹ ∈ P := hsec.normP r r.2 z z.2
  have hact := hκ.act r z ⟨(r : G) * z * (r : G)⁻¹, hy⟩ rfl
  have hcc : c = ⟨(r : G) * z * (r : G)⁻¹, hy⟩ * z⁻¹ := by
    apply Subtype.ext
    simp [hc, commutatorElement_def]
  rw [hcc, map_mul, map_inv, hact, toAdd_mul, toAdd_inv, toAdd_ofAdd]
  abel

theorem sec715Spl_smul_eq (hsec : SecHyp R P I) (hκ : IsSecMod R P I Mm κ) (r : ↥R) (z : ↥P)
    (h : ⁅(r : G), (z : G)⁆ ∈ I) :
    r • Multiplicative.toAdd (κ z) = Multiplicative.toAdd (κ z) := by
  have h1 := sec715Spl_comm_eq hsec hκ r z ⟨⁅(r : G), (z : G)⁆, sec715Spl_comm_mem_P hsec r z⟩
    rfl
  have h2 : κ ⟨⁅(r : G), (z : G)⁆, sec715Spl_comm_mem_P hsec r z⟩ = 1 := (hκ.ker _).mpr h
  rw [h2, toAdd_one] at h1
  exact sub_eq_zero.mp h1

theorem sec715Spl_sq_smul (hsec : SecHyp R P I) (hκ : IsSecMod R P I Mm κ) (x : ↥R)
    (hx : ∀ z ∈ P, ⁅((x * x : ↥R) : G), z⁆ ∈ I) (m : Mm) : x • x • m = m := by
  obtain ⟨z, hz⟩ := hκ.surj (Multiplicative.ofAdd m)
  have hm : m = Multiplicative.toAdd (κ z) := by rw [hz]; rfl
  rw [hm, ← mul_smul]
  exact sec715Spl_smul_eq hsec hκ _ z (hx z z.2)

theorem sec715Spl_full (hsec : SecHyp R P I) (hκ : IsSecMod R P I Mm κ) {L V₀ : Subgroup G}
    (x : ↥R) (hI : I ≤ V₀)
    (hfull : ∀ a ∈ P ⊓ L, ∃ z ∈ P, ⁅(x : G), z⁆ * a⁻¹ ∈ V₀) :
    ∀ a ∈ secSub κ (P ⊓ L), ∃ m : Mm,
      a - (x • m - m) ∈ secSub κ V₀ := by
  intro a ha
  obtain ⟨w, hw, hwa⟩ := mem_secSub.mp ha
  obtain ⟨z, hz, hzV⟩ := hfull w hw
  let zP : ↥P := ⟨z, hz⟩
  let c : ↥P := ⟨⁅(x : G), (z : G)⁆, sec715Spl_comm_mem_P hsec x zP⟩
  have hcm := sec715Spl_comm_eq hsec hκ x zP c rfl
  refine ⟨Multiplicative.toAdd (κ zP), mem_secSub.mpr ⟨w * c⁻¹, ?_, ?_⟩⟩
  · have e : ((w * c⁻¹ : ↥P) : G) = (⁅(x : G), z⁆ * (w : G)⁻¹)⁻¹ := by
      simp [c, mul_inv_rev]
    rw [e]
    exact V₀.inv_mem hzV
  · rw [map_mul, map_inv, hwa, hcm, ofAdd_sub, ofAdd_toAdd, div_eq_mul_inv]

theorem sec715Spl_K (hsec : SecHyp R P I) (hκ : IsSecMod R P I Mm κ) {L : Subgroup G}
    (x : ↥R)
    (hK : ∀ l ∈ L, ∀ z ∈ P, ∃ z' ∈ P, ⁅l, z⁆ * ⁅(x : G), z'⁆⁻¹ ∈ I) :
    ∀ l : ↥R, (l : G) ∈ L → ∀ m : Mm, ∃ m' : Mm, l • m - m = x • m' - m' := by
  intro l hl m
  obtain ⟨z, hz⟩ := hκ.surj (Multiplicative.ofAdd m)
  have hm : m = Multiplicative.toAdd (κ z) := by rw [hz]; rfl
  obtain ⟨z', hz', hzI⟩ := hK l hl z z.2
  let z'P : ↥P := ⟨z', hz'⟩
  refine ⟨Multiplicative.toAdd (κ z'P), ?_⟩
  let c₁ : ↥P := ⟨⁅(l : G), (z : G)⁆, sec715Spl_comm_mem_P hsec l z⟩
  let c₂ : ↥P := ⟨⁅(x : G), (z' : G)⁆, sec715Spl_comm_mem_P hsec x z'P⟩
  rw [hm, sec715Spl_comm_eq hsec hκ l z c₁ rfl, sec715Spl_comm_eq hsec hκ x z'P c₂ rfl]
  have : κ c₁ = κ c₂ := by
    rw [hκ.eq_iff]
    simpa [c₁, c₂] using hzI
  rw [this]

theorem sec715Spl_card [Finite ↥P] (hκ : IsSecMod R P I Mm κ) {A V₀ : Subgroup G} (hIV₀ : I ≤ V₀)
    (hV₀A : V₀ ≤ A) (hAP : A ≤ P) (hcard : Nat.card ↥A ^ 2 = Nat.card ↥V₀ * Nat.card ↥P) :
    Nat.card ↥(secSub κ A) ^ 2 = Nat.card Mm * Nat.card ↥(secSub κ V₀) := by
  have hIP : I ≤ P := hIV₀.trans (hV₀A.trans hAP)
  haveI : Finite ↥I :=
    Finite.of_injective (Subgroup.inclusion hIP) (Subgroup.inclusion_injective hIP)
  have hpos : 0 < Nat.card ↥I := Nat.card_pos
  have h1 := natCard_secSub_mul hIP hκ (hIV₀.trans hV₀A) hAP
  have h2 := natCard_secSub_mul hIP hκ hIV₀ (hV₀A.trans hAP)
  have h3 := natCard_eq_of_isSecMod hIP hκ
  rw [← h1, ← h2, h3] at hcard
  have h4 : Nat.card ↥I * Nat.card ↥I * Nat.card ↥(secSub κ A) ^ 2 =
      Nat.card ↥I * Nat.card ↥I * (Nat.card Mm * Nat.card ↥(secSub κ V₀)) := by
    calc Nat.card ↥I * Nat.card ↥I * Nat.card ↥(secSub κ A) ^ 2
        = (Nat.card ↥(secSub κ A) * Nat.card ↥I) ^ 2 := by ring
      _ = Nat.card ↥(secSub κ V₀) * Nat.card ↥I * (Nat.card ↥I * Nat.card Mm) := hcard
      _ = _ := by ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hpos hpos) h4

end ActLemmas

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def Sec715ZNCommStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → OmegaPlusNat hc t 4 → n = 16 →
    ∀ Z0 Zn : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    IsCentrePre Zn (hc.CN t) Q → Zn ≠ Z0 → ¬ ⁅hc.CN t, hc.CN t⁆ ≤ Q →
    ∀ r : G, Sec7A hc t r → ∀ L : Subgroup G,
      (L = LB M Q B ∨ L = LB M Q (conjSubgroup r B)) →
      ∃ x ∈ L, (∀ a ∈ Zn ⊓ L, ∃ z ∈ Zn, ⁅x, z⁆ * a⁻¹ ∈ Z0) ∧
        ∀ l ∈ L, ∀ z ∈ Zn, ∃ z' ∈ Zn, ⁅l, z⁆ * ⁅x, z'⁆⁻¹ ∈ Q

theorem sec715Split_of_comm (hComm : Sec715ZNCommStatement) (h51 : Stroth51Statement)
    (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement) :
    Sec715SplitStatement := by
  intro G _ _ M Q Z B hc n t hs hp4 hn16 Z0 hZ0 hnc Zn hZn hne
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨hZ0Zn, hZnN, hZnn⟩ := sec715Spl_Zn_facts hc hs hZ0 hZn
  obtain ⟨r, hr, hdA, hcard₁, hcard₂, hgen⟩ := sec715Spl_data h51 hA hPts hc hs hp4 hZ0 hZn
  have hCNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hQM : ∀ g ∈ M, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) y).mp hy
  have hQn : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ => hQM ρ (hRM hρ)
  have hQN : Q ≤ hc.CN t := sec8_Q_le_CN hc ht
  have hQZn : Q ≤ Zn := hZn.Q_le hQN fun ρ hρ => hQn ρ (hCNR hρ)
  have hLA : LB M Q (conjSubgroup r B) = conjSubgroup r (LB M Q B) :=
    hc.LB_conj (hRM hr.mem)
  have hsqA : ∀ a ∈ LB M Q (conjSubgroup r B), a ^ 2 ∈ Q := by
    intro a ha
    rw [hLA, mem_conjSubgroup] at ha
    have h1 := hc.sq_mem_Q_of_mem_LB ha
    have e : a ^ 2 = r * (r⁻¹ * a * r) ^ 2 * r⁻¹ := by
      simp only [pow_two]
      group
    rw [e]
    exact hQM r (hRM hr.mem) _ h1
  have hsq : ∀ z ∈ Zn, z ^ 2 ∈ Q := by
    have key : ∀ z, z ∈ Subgroup.closure
        (((Zn ⊓ LB M Q B : Subgroup G) : Set G) ∪
          ((Zn ⊓ LB M Q (conjSubgroup r B) : Subgroup G) : Set G)) → z ∈ Zn ∧ z ^ 2 ∈ Q := by
      intro z hz'
      induction hz' using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with hx | hx
        · exact ⟨(Subgroup.mem_inf.mp hx).1, hc.sq_mem_Q_of_mem_LB (Subgroup.mem_inf.mp hx).2⟩
        · exact ⟨(Subgroup.mem_inf.mp hx).1, hsqA x (Subgroup.mem_inf.mp hx).2⟩
      | one => exact ⟨Zn.one_mem, by simpa using Q.one_mem⟩
      | mul x y _ _ ihx ihy =>
        refine ⟨Zn.mul_mem ihx.1 ihy.1, ?_⟩
        have hxM : x ∈ M := hRM (hCNR (hZnN ihx.1))
        have hw : ⁅y, x⁆ ∈ Q := hZn.comm_mem ihy.1 (hZnN ihx.1)
        have e : (x * y) ^ 2 = (x * ⁅y, x⁆ * x⁻¹) * x ^ 2 * y ^ 2 := by
          simp only [pow_two, commutatorElement_def]
          group
        rw [e]
        exact Q.mul_mem (Q.mul_mem (hQM x hxM _ hw) ihx.2) ihy.2
      | inv x _ ih =>
        exact ⟨Zn.inv_mem ih.1, by rw [inv_pow]; exact Q.inv_mem ih.2⟩
    intro z hz
    refine (key z ?_).2
    rw [← Subgroup.sup_eq_closure, hdA.2.2.2.2.1]
    exact hz
  have hcomm : ∀ x ∈ Zn, ∀ y ∈ Zn, ⁅x, y⁆ ∈ Q := fun x hx y hy => hZn.comm_mem hx (hZnN hy)
  have hsec : SecHyp (Rt M (LB M Q B) t) Zn Q := ⟨hQZn, hcomm, hsq, hZnn, hQn⟩
  obtain ⟨Mq, iM, iA, κ, hκ⟩ := exists_sectionModule hsec
  haveI : Finite Mq := hκ.finite
  have hQZ0 : Q ≤ Z0 := hZ0.Q_le (hc.Q_le_Rt ht) hQn
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hL2R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := le_sup_right.trans hr.gen.ge
  obtain ⟨x₁, hx₁L, hfull₁, hK₁⟩ := hComm G M Q Z B hc n t hs hp4 hn16 Z0 Zn hZ0 hZn hne hnc r hr
    (LB M Q B) (Or.inl rfl)
  obtain ⟨x₂, hx₂L, hfull₂, hK₂⟩ := hComm G M Q Z B hc n t hs hp4 hn16 Z0 Zn hZ0 hZn hne hnc r hr
    (LB M Q (conjSubgroup r B)) (Or.inr rfl)
  let x₁R : ↥(Rt M (LB M Q B) t) := ⟨x₁, hLR hx₁L⟩
  let x₂R : ↥(Rt M (LB M Q B) t) := ⟨x₂, hL2R hx₂L⟩
  have hQZ : ∀ q ∈ Q, ∀ z ∈ Zn, ⁅q, z⁆ ∈ Q := fun q hq z hz => by
    rw [← commutatorElement_inv]
    exact Q.inv_mem (hZn.comm_mem hz (hQN hq))
  have hsq₁ : ∀ z ∈ Zn, ⁅((x₁R * x₁R : ↥(Rt M (LB M Q B) t)) : G), z⁆ ∈ Q := by
    intro z hz
    have : ((x₁R * x₁R : ↥(Rt M (LB M Q B) t)) : G) ∈ Q := by
      simpa [x₁R, pow_two] using hc.sq_mem_Q_of_mem_LB hx₁L
    exact hQZ _ this z hz
  have hsq₂ : ∀ z ∈ Zn, ⁅((x₂R * x₂R : ↥(Rt M (LB M Q B) t)) : G), z⁆ ∈ Q := by
    intro z hz
    have : ((x₂R * x₂R : ↥(Rt M (LB M Q B) t)) : G) ∈ Q := by
      simpa [x₂R, pow_two] using hsqA x₂ hx₂L
    exact hQZ _ this z hz
  have hsqS₁ := sec715Spl_sq_smul hsec hκ x₁R hsq₁
  have hsqS₂ := sec715Spl_sq_smul hsec hκ x₂R hsq₂
  have hfS₁ := sec715Spl_full hsec hκ (L := LB M Q B) (V₀ := Z0) x₁R hQZ0 hfull₁
  have hfS₂ := sec715Spl_full hsec hκ (L := LB M Q (conjSubgroup r B)) (V₀ := Z0) x₂R hQZ0
    hfull₂
  have hKS₁ := sec715Spl_K hsec hκ (L := LB M Q B) x₁R hK₁
  have hKS₂ := sec715Spl_K hsec hκ (L := LB M Q (conjSubgroup r B)) x₂R hK₂
  obtain ⟨hI₁, hA₁P, hI₂, hA₂P, hsupA, hinfA, -⟩ := hdA
  have hVA₁ : secSub κ Z0 ≤ secSub κ (Zn ⊓ LB M Q B) := secSub_mono hI₁
  have hVA₂ : secSub κ Z0 ≤ secSub κ (Zn ⊓ LB M Q (conjSubgroup r B)) := secSub_mono hI₂
  have hinf : secSub κ (Zn ⊓ LB M Q B) ⊓ secSub κ (Zn ⊓ LB M Q (conjSubgroup r B)) =
      secSub κ Z0 := by
    rw [← secSub_inf hκ (hQZ0.trans hI₁), hinfA]
  have hsup : secSub κ (Zn ⊓ LB M Q B) ⊔ secSub κ (Zn ⊓ LB M Q (conjSubgroup r B)) = ⊤ := by
    rw [← secSub_sup hA₁P hA₂P, hsupA, secSub_eq_top hκ]
  have hcardM₁ := sec715Spl_card hκ hQZ0 hI₁ hA₁P hcard₁
  have hcardM₂ := sec715Spl_card hκ hQZ0 hI₂ hA₂P hcard₂
  have hV : ∀ g : ↥(Rt M (LB M Q B) t), ∀ v ∈ secSub κ Z0, g • v = v := by
    intro g v hv
    obtain ⟨z, hzZ0, hzv⟩ := mem_secSub.mp hv
    have hv' : v = Multiplicative.toAdd (κ z) := by rw [hzv]; rfl
    rw [hv']
    apply sec715Spl_smul_eq hsec hκ
    rw [← commutatorElement_inv]
    exact Q.inv_mem (hZ0.comm_mem hzZ0 g.2)
  obtain ⟨Y, hYinf, hYsup, hYinv⟩ := exists_complement_of_full_commutators hκ.two (secSub κ Z0)
    (secSub κ (Zn ⊓ LB M Q B)) (secSub κ (Zn ⊓ LB M Q (conjSubgroup r B)))
    {l : ↥(Rt M (LB M Q B) t) | (l : G) ∈ LB M Q B}
    {l : ↥(Rt M (LB M Q B) t) | (l : G) ∈ LB M Q (conjSubgroup r B)} x₁R x₂R hV hVA₁ hVA₂ hinf
    hsup hsqS₁ hsqS₂ hfS₁ hfS₂ hcardM₁ hcardM₂ hKS₁ hKS₂
  obtain ⟨U, hQU, hUZn, hUY⟩ := exists_secSub_eq hQZn hκ Y
  have hnormL : ∀ L : Subgroup G, L ≤ Rt M (LB M Q B) t →
      (∀ l : ↥(Rt M (LB M Q B) t), (l : G) ∈ L → ∀ y ∈ Y, l • y ∈ Y) →
      L ≤ Subgroup.normalizer (U : Set G) := by
    intro L hL hinv l hl
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    have hyZ : y ∈ Zn := hUZn hy
    let yP : ↥Zn := ⟨y, hyZ⟩
    have h1 : Multiplicative.toAdd (κ yP) ∈ Y := by
      rw [← hUY]
      exact (toAdd_mem_secSub_iff hκ hQU yP).mpr hy
    have h2 := hinv ⟨l, hL hl⟩ hl _ h1
    have h4 : Multiplicative.toAdd (κ ⟨l * y * l⁻¹, hZnn l (hL hl) y hyZ⟩) ∈ Y := by
      have := hκ.act ⟨l, hL hl⟩ yP ⟨l * y * l⁻¹, hZnn l (hL hl) y hyZ⟩ rfl
      rw [this, toAdd_ofAdd]
      exact h2
    rw [← hUY] at h4
    exact (toAdd_mem_secSub_iff hκ hQU _).mp h4
  refine ⟨U, hQU, hUZn, ?_, ?_, ?_⟩
  · intro ρ hρ
    have hnorm : Rt M (LB M Q B) t ≤ Subgroup.normalizer (U : Set G) := by
      refine hgen.trans (sup_le ?_ (sup_le ?_ ?_))
      · intro k hk
        refine Subgroup.mem_normalizer_fintype fun y hy => ?_
        have hyZ : y ∈ Zn := hUZn hy
        have e : k * y * k⁻¹ = ⁅k, y⁆ * y := by simp [commutatorElement_def]
        rw [e]
        have hq : ⁅k, y⁆ ∈ Q := by
          rw [← commutatorElement_inv]
          exact Q.inv_mem (hZn.comm_mem hyZ hk)
        exact U.mul_mem (hQU hq) hy
      · exact hnormL _ hLR fun l hl y hy => hYinv l (Or.inl hl) y hy
      · exact hnormL _ hL2R fun l hl y hy => hYinv l (Or.inr hl) y hy
    exact conjSubgroup_eq_self_iff.mpr (hnorm hρ)
  · have h1 : secSub κ (U ⊓ Z0) = secSub κ Q := by
      rw [secSub_inf hκ hQU, hUY, hYinf, secSub_eq_bot hκ]
    exact (secSub_inj hκ (le_inf hQU hQZ0) (inf_le_left.trans hUZn) le_rfl hQZn).mp h1
  · have h1 : secSub κ (U ⊔ Z0) = secSub κ Zn := by
      rw [secSub_sup hUZn hZ0Zn, hUY, hYsup, secSub_eq_top hκ]
    exact (secSub_inj hκ (hQU.trans le_sup_left) (sup_le hUZn hZ0Zn) hQZn le_rfl).mp h1

end CFSG.RankThree.GF2n.Stroth80
