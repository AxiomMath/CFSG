module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138VCube
import CFSG.RankThree.PartTwo.Sec4.Ronan148LCubeLift
import CFSG.RankThree.PartTwo.Sec4.Ronan148LCubeFrame
import CFSG.RankThree.PartTwo.Sec13.Ronan138BFix81
import CFSG.RankThree.PartTwo.Sec13.Ronan138S131
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SKSetup
import CFSG.RankThree.PartTwo.Sec13.Ronan138SPGL
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists
import CFSG.RankThree.PartTwo.Sec13.Item136Moreover
import CFSG.RankThree.PartTwo.Sec13.Item13K410
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec11.Item116H3Rank
import CFSG.RankThree.PartTwo.Sec11.Item1119StepsProofCenter
import CFSG.RankThree.PartTwo.Sec11.AutThree1129.L3
import CFSG.RankThree.PartTwo.Sec4.Item424ProofInner
import CFSG.RankThree.PartTwo.Sec15.Item158CartanProofTorus
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138V

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open Matrix (ProjGenLinGroup GeneralLinearGroup)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_mem_inSubgroup_theta {L : Subgroup G} {x : G}
    (hx : x ∈ inSubgroup (aschbacherSolvableCore 3) L) {k : ℕ} (hk : x ^ (3 ^ k) = 1) :
    x = 1 := by
  obtain ⟨t, ht, rfl⟩ := hx
  have h1 : orderOf (⟨t, ht⟩ : aschbacherSolvableCore 3 L) ∣ 3 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    apply Subtype.ext
    simpa using hk
  have h2 := orderOf_dvd_natCard (⟨t, ht⟩ : aschbacherSolvableCore 3 L)
  have hcop : Nat.Coprime (3 ^ k) (Nat.card (aschbacherSolvableCore 3 L)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (KFacts.not_three_dvd_card_aschbacherSolvableCore L))
  have h3 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have : t = 1 := congrArg Subtype.val h3
  simp [this]

theorem mem_normalizer_zpowers_of_commute {e g : G} (h : e * g = g * e) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers e : Set G) := by
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact (Commute.zpow_left (show Commute e g from h) k).eq

theorem exists_isSylowOf_ge {p : ℕ} [Fact p.Prime] {X D : Subgroup G} (hX : IsPGroup p X)
    (hXD : X ≤ D) : ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P D ∧ X ≤ P := by
  have hX' : IsPGroup p (X.subgroupOf D) := hX.comap_subtype
  obtain ⟨Q, hQ⟩ := hX'.exists_le_sylow
  refine ⟨(Q : Subgroup D).map D.subtype, ⟨Q, rfl⟩, ?_⟩
  intro x hx
  exact ⟨⟨x, hXD hx⟩, hQ (show (⟨x, hXD hx⟩ : D) ∈ X.subgroupOf D from hx), rfl⟩

theorem card_le_of_isSylowOf {p : ℕ} [Fact p.Prime] {Q S N : Subgroup G} (hQ : IsPGroup p Q)
    (hQN : Q ≤ N) (hS : CFSG.ABGLocalTools.IsSylowOf p S N) : Nat.card Q ≤ Nat.card S := by
  obtain ⟨S', hS', hQS'⟩ := exists_isSylowOf_ge hQ hQN
  rw [hS.card_eq, ← hS'.card_eq]
  exact Subgroup.card_le_of_le hQS'

theorem card_le_mul_card_inf {L X : Subgroup G} (hXN : X ≤ Subgroup.normalizer (L : Set G))
    (hX3 : IsPGroup 3 X)
    (hbound : ∀ R : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)), IsPGroup 3 R →
      Nat.card R ≤ 27) :
    Nat.card X ≤ 27 * Nat.card (X ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) := by
  set ρ : X →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
    (Sec15.Proof158Cartan.actBar L).comp (Subgroup.inclusion hXN) with hρ
  have hrange : Nat.card ρ.range ≤ 27 :=
    hbound _ (hX3.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective)
  have hker : ρ.ker.map X.subtype = X ⊓ Sec4.thetaQuotCentralizer L := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, (Sec15.Proof158Cartan.actBar_eq_one_iff (Subgroup.inclusion hXN x)).mp
        (MonoidHom.mem_ker.mp hx)⟩
    · rintro ⟨hgX, hgC⟩
      refine ⟨⟨g, hgX⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
      exact (Sec15.Proof158Cartan.actBar_eq_one_iff ⟨g, hXN hgX⟩).mpr hgC
  have hkc : Nat.card ρ.ker = Nat.card (X ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) := by
    rw [← hker, Subgroup.card_map_of_injective X.subtype_injective]
  have h := Subgroup.card_ker_mul_card_range ρ
  rw [hkc] at h
  calc Nat.card X = Nat.card (X ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) *
        Nat.card ρ.range := h.symm
    _ ≤ Nat.card (X ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) * 27 :=
        Nat.mul_le_mul_left _ hrange
    _ = 27 * Nat.card (X ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) := mul_comm _ _

section Hyp

variable {A L E F : Subgroup G} {c : G}

theorem card_le_27_of_hyp138 (hH : Hyp138 A c L E) (hPGL : Sec8.IsZ3PGLThreePi (lBarA c L E)) :
    ∀ R : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)), IsPGroup 3 R →
      Nat.card R ≤ 27 := by
  intro R hR
  obtain ⟨h, hL3, hcE, hE3, -, hEN, -, -, hC⟩ := hH
  have hLq := Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  obtain ⟨p, e, _, he, hiso⟩ := hL3
  have h9 := Sec13.not_modNine_of_isTypeCOn h hcE hE3 hEN hC hPGL he hiso
  obtain ⟨π, K, _, hK, hq, ⟨φ⟩⟩ := Sec13.exists_projImage_model he hiso
  have hq2 : 2 < p ^ e := Item138Proof.two_lt_of_mulEquiv hLq hK hq φ
  have h9' : ¬ Sec4.ModNine π (p ^ e) := by
    cases π <;> simp only [Sec4.ModNine, cond_true, cond_false] <;> omega
  have h1 := Sec11.AutThree1129.card_le_27_of_model hK hq hq2 h9'
    (R.map (MulAut.congr φ).toMonoidHom) (hR.map _)
  rwa [Subgroup.card_map_of_injective (MulAut.congr φ).injective] at h1

theorem facts_F_of_hyp138 (hH : Hyp138 A c L E) (hF : IsF138N L E F)
    (hPGL : Sec8.IsZ3PGLThreePi (lBarA c L E)) :
    c ∈ F ∧ Subgroup.zpowers c ⊔ (F ⊓ L) = F ∧
      (∀ x ∈ L, x ∈ Sec4.thetaQuotCentralizer L → x ^ 3 = 1 → x = 1) ∧
      c ∈ Sec4.thetaQuotCentralizer L ∧ c ∉ L := by
  obtain ⟨-, -, -, -, -, -, -, hcF, -, -, -⟩ := Ronan138S.exists_frame138 hH hF hPGL
  obtain ⟨h, hL3, -, -, -, -, -, -, -⟩ := hH
  obtain ⟨⟨-, hF3, hF27, -, -⟩, hFL9⟩ := hF
  have hL := h.mem_thetaComponentsAt
  have hLc := h.le_centralizer
  have hc := h.orderOf_eq
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hLq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hL
  have hZ := Sec11.Item1119StepsProof.center_eq_bot_of_isLThreePi hLq hL3
  have hLc' : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hLc hl)
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun l hl => hLc' l hl)
  have hcθ : c ∈ Sec4.thetaQuotCentralizer L :=
    (Sec15.Proof158Cartan.actBar_eq_one_iff ⟨c, hcN⟩).mp
      (Sec15.Proof158Cartan.actBar_eq_one_of_commute hcN hLc')
  have hθL : ∀ x ∈ L, x ∈ Sec4.thetaQuotCentralizer L → x ^ 3 = 1 → x = 1 :=
    fun x hxL hx hx3 => eq_one_of_mem_inSubgroup_theta (k := 1)
      (Sec4.Item424Proof.mem_theta_of_mem_thetaQuotCentralizer hZ hxL hx) (by simpa using hx3)
  have hcL : c ∉ L := fun hcL => h.ne_one (hθL c hcL hcθ hc3)
  have hFLc : Subgroup.zpowers c ⊓ (F ⊓ L) = ⊥ := by
    have hdvd : Nat.card (Subgroup.zpowers c ⊓ (F ⊓ L) : Subgroup G) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers c ⊓ (F ⊓ L) ≤
        Subgroup.zpowers c)
      rwa [Nat.card_zpowers, hc] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : Subgroup.zpowers c ⊓ (F ⊓ L) = Subgroup.zpowers c :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, Nat.card_zpowers, hc])
      have hcm : c ∈ Subgroup.zpowers c ⊓ (F ⊓ L) := by
        rw [heq]
        exact Subgroup.mem_zpowers c
      exact hcL hcm.2.2
  have hFcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF3.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcFL : Subgroup.zpowers c ≤ Subgroup.normalizer ((F ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    intro f hf
    exact hFcomm f hf.1 c hcF
  have hFeq : Subgroup.zpowers c ⊔ (F ⊓ L) = F := by
    have hle : Subgroup.zpowers c ⊔ (F ⊓ L) ≤ F :=
      sup_le (Subgroup.zpowers_le.mpr hcF) inf_le_left
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have := Sec6.card_sup_mul_card_inf hcFL
    rw [hFLc, Subgroup.card_bot, mul_one, Nat.card_zpowers, hc, hFL9] at this
    rw [hF27, this]
  exact ⟨hcF, hFeq, hθL, hcθ, hcL⟩

theorem normalizer_zpowers_le_normalizer_L (hH : Hyp138 A c L E) (hF : IsF138N L E F)
    (hPGL : Sec8.IsZ3PGLThreePi (lBarA c L E))
    (hFmax : ∀ F' : Subgroup G, CFSG.Assembly.IsElemAbelian 3 F' → F ≤ F' → F' = F) :
    Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨-, hFeq, -, -, -⟩ := facts_F_of_hyp138 hH hF hPGL
  obtain ⟨h, hL3, -, -, -, -, -, -, -⟩ := hH
  obtain ⟨⟨-, hF3, -, -, -⟩, hFL9⟩ := hF
  have hL := h.mem_thetaComponentsAt
  have hc := h.orderOf_eq
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hLq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hL
  have hZ := Sec11.Item1119StepsProof.center_eq_bot_of_isLThreePi hLq hL3
  have hFcL : F ≤ Subgroup.zpowers c ⊔ L := hFeq ▸ sup_le_sup_left inf_le_right _
  have h3L : 3 ∣ Nat.card L := by
    have h1 := Subgroup.card_dvd_of_le (inf_le_right : F ⊓ L ≤ L)
    rw [hFL9] at h1
    exact (show 3 ∣ 9 by norm_num).trans h1
  intro g hg
  have hgc : g * c * g⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp hg c).mp (Subgroup.mem_zpowers c)
  have hLg := Sec11.map_conj_mem_thetaComponentsAt hc3 hL hgc
  have h3Lg : 3 ∣ Nat.card (L.map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact h3L
  exact map_conj_eq_iff_mem_normalizer.mp
    (eq_of_mem_thetaComponentsAt_of_maximal hc hL hZ hFcL hF3
      (fun B hB hFB => (hFmax B hB hFB) ▸ le_rfl) hLg h3Lg)

theorem commute_and_mem_zpowers (hH : Hyp138 A c L E) (hF : IsF138N L E F)
    (hPGL : Sec8.IsZ3PGLThreePi (lBarA c L E))
    (hFmax : ∀ F' : Subgroup G, CFSG.Assembly.IsElemAbelian 3 F' → F ≤ F' → F' = F)
    {X : Subgroup G} (hX3 : IsPGroup 3 X) (hFX : F ≤ X)
    (hXc : X ≤ Subgroup.centralizer ({c} : Set G))
    (hXN : X ≤ Subgroup.normalizer (L : Set G)) :
    (∀ v ∈ X ⊓ Sec4.thetaQuotCentralizer L, ∀ f ∈ F, f * v = v * f) ∧
      ∀ v ∈ X ⊓ Sec4.thetaQuotCentralizer L, v ^ 3 = 1 → v ∈ Subgroup.zpowers c := by
  obtain ⟨-, hFeq, hθL, hcθ, -⟩ := facts_F_of_hyp138 hH hF hPGL
  obtain ⟨⟨-, hF3, -, -, -⟩, -⟩ := hF
  have hFcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF3.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcF : c ∈ F := hFeq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have hcFL : Subgroup.zpowers c ≤ Subgroup.normalizer ((F ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    intro f hf
    exact hFcomm f hf.1 c hcF
  have hX3elt : ∀ w ∈ X, ∃ k : ℕ, w ^ (3 ^ k) = 1 := fun w hw => by
    obtain ⟨k, hk⟩ := hX3 ⟨w, hw⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hcentF : ∀ w ∈ X ⊓ Sec4.thetaQuotCentralizer L, ∀ f ∈ F, f * w = w * f := by
    intro w hw
    have hwθ := Sec6.mem_thetaQuotCentralizer_iff.mp hw.2
    have hFw : F ≤ Subgroup.centralizer ({w} : Set G) := by
      rw [← hFeq]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hXc hw.1)).symm
      · intro f hf
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hθ := hwθ.2 f hf.2
        have hPm : f⁻¹ * (w * f * w⁻¹) ∈ X :=
          X.mul_mem (X.inv_mem (hFX hf.1)) (X.mul_mem (X.mul_mem hw.1 (hFX hf.1)) (X.inv_mem hw.1))
        obtain ⟨k, hk⟩ := hX3elt _ hPm
        have h1 := eq_one_of_mem_inSubgroup_theta hθ hk
        have h2 : w * f * w⁻¹ = f := by
          calc w * f * w⁻¹ = f * (f⁻¹ * (w * f * w⁻¹)) := by group
            _ = f := by rw [h1, mul_one]
        calc f * w = (w * f * w⁻¹) * w := by rw [h2]
          _ = w * f := by group
    intro f hf
    exact Subgroup.mem_centralizer_singleton_iff.mp (hFw hf)
  refine ⟨hcentF, fun w hw hw3 => ?_⟩
  have hwF : w ∈ F := by
    have hcomm : ∀ a ∈ F, ∀ b ∈ Subgroup.zpowers w, a * b = b * a := by
      intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_right (show Commute a w from hcentF w hw a ha) k).eq
    have hFw := CFSG.Open.IsElemAbelian.sup_of_commute hF3
      (CFSG.Open.isElemAbelian_zpowers hw3) hcomm
    have heq := hFmax _ hFw le_sup_left
    exact heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
  have hwm : w ∈ (Subgroup.zpowers c : Set G) * ((F ⊓ L : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcFL, hFeq]
    exact hwF
  obtain ⟨a, ha, f, hf, rfl⟩ := hwm
  have hfθ : f ∈ Sec4.thetaQuotCentralizer L := by
    have : f = a⁻¹ * (a * f) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _
      ((Subgroup.zpowers_le.mpr hcθ) ha)) hw.2
  have hf1 : f = 1 := hθL f hf.2 hfθ (hF3.2 f hf.1)
  subst hf1
  simpa using ha

end Hyp

theorem mem_zpowers_of_actsPGL {K T : Subgroup G} {c x₀ t : G} {π : Bool} {p f : ℕ} {Fld : Type}
    [Field Fld] (hPi : Sec4.PiField π p f Fld) (hq : Sec4.ModThree π (p ^ f))
    {ψ : K ⧸ aschbacherSolvableCore 3 K ≃* projImage (Sec4.slPi π 3 (p ^ f) Fld)}
    [Group.IsPerfect (projImage (Sec4.slPi π 3 (p ^ f) Fld))] {y₀ M : GL (Fin 3) Fld}
    (hx₀ : Ronan138S.ActsPGL ψ x₀ y₀) (hy₀3 : Sec4.Type123 π (p ^ f) Fld y₀ 3) (hc3 : c ^ 3 = 1)
    (hcK : c ∉ Sec4.thetaQuotCentralizer K) (hx₀c : x₀ * c = c * x₀)
    (hx₀T : ∀ v ∈ T, x₀ * v * x₀⁻¹ ∈ T)
    (hTK : ∀ v ∈ T, v ∈ Sec4.thetaQuotCentralizer K → v = 1)
    (hTc : ∀ v ∈ T, v ^ 3 = 1 → v ∈ Subgroup.zpowers c) (hT3 : IsPGroup 3 T) (htT : t ∈ T)
    (htM : Ronan138S.ActsPGL ψ t M) : t ∈ Subgroup.zpowers c := by
  have hπ : π = false → UnitaryFieldData p f Fld := fun h => by subst h; exact hPi.unitary
  by_contra htc
  obtain ⟨k, hk⟩ := hT3 ⟨t, htT⟩
  have hk' : t ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, -, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk')
  have hj2 : 2 ≤ j := by
    by_contra hj2
    apply htc
    apply hTc t htT
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hjo]
    interval_cases j <;> norm_num
  have hdvd : 3 ^ (j - 2) ∣ orderOf t := by
    rw [hjo]
    exact pow_dvd_pow 3 (by omega)
  set t₁ := t ^ 3 ^ (j - 2) with ht₁
  have ht₁o : orderOf t₁ = 9 := by
    rw [ht₁, orderOf_pow_of_dvd (by positivity) hdvd, hjo, Nat.pow_div (by omega) (by norm_num),
      show j - (j - 2) = 2 by omega]
  have ht₁T : t₁ ∈ T := pow_mem htT _
  have hu3 : (t₁ ^ 3) ^ 3 = 1 := by
    rw [← pow_mul, show 3 * 3 = 9 by rfl, ← ht₁o, pow_orderOf_eq_one]
  have hu1 : t₁ ^ 3 ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [ht₁o] at this
    norm_num at this
  obtain ⟨n, hn⟩ := Ronan138S.exists_pow_eq_of_mem_zpowers (hTc _ (pow_mem ht₁T 3) hu3)
  have hM₁ : Ronan138S.ActsPGL ψ t₁ (M ^ 3 ^ (j - 2)) := htM.pow hπ _
  have hn0 : n % 3 ≠ 0 := by
    intro h0
    apply hu1
    rw [← hn, ← Nat.mod_add_div n 3, h0, zero_add, pow_mul, hc3, one_pow]
  obtain ⟨t₂, ht₂T, M₂, ht₂M, ht₂c⟩ : ∃ t₂ ∈ T, ∃ M₂ : GL (Fin 3) Fld,
      Ronan138S.ActsPGL ψ t₂ M₂ ∧ t₂ ^ 3 = c := by
    rcases (by omega : n % 3 = 1 ∨ n % 3 = 2) with h1 | h2
    · refine ⟨t₁, ht₁T, _, hM₁, ?_⟩
      rw [← hn, ← Nat.mod_add_div n 3, h1, pow_add, pow_mul, hc3, one_pow, mul_one, pow_one]
    · refine ⟨t₁⁻¹, inv_mem ht₁T, _, hM₁.inv, ?_⟩
      have hc2 : c ^ 2 * c = 1 := by rw [← pow_succ, hc3]
      rw [inv_pow, ← hn, ← Nat.mod_add_div n 3, h2, pow_add, pow_mul, hc3, one_pow, mul_one,
        eq_inv_of_mul_eq_one_left hc2, inv_inv]
  exact false_of_actsPGL hPi hq hx₀ hy₀3 ht₂M ht₂c hc3 hcK hx₀c
    (mul_mem (hx₀T _ ht₂T) (inv_mem ht₂T)) hTK hTc

section Main

theorem not_modNine_of_cfg (h131 : Item131)
    {A : Subgroup G} {c : G} {L E F : Subgroup G} (hH : Hyp138 A c L E)
    (hPGL : Sec8.IsZ3PGLThreePi (lBarA c L E)) (hF : IsF138N L E F)
    (hFmax : ∀ F' : Subgroup G, CFSG.Assembly.IsElemAbelian 3 F' → F ≤ F' → F' = F)
    {e : G} {K : Subgroup G} (heΩ : Subgroup.zpowers e ∈ omegaA E) (hK : K ∈ lA E e)
    (heF : e ∈ F) (hec : e ∉ Subgroup.zpowers c) (heL : e ∉ L)
    (hPGLK : Sec8.IsZ3PGLThreePi (lBarA e K E)) (hEF3 : IsPGroup 3 ↥(E ⊔ F))
    {x₀ : G} (hx₀E : x₀ ∈ E) {π : Bool} {p f : ℕ} {Fld : Type} [Field Fld]
    (hPi : Sec4.PiField π p f Fld) (hq : Sec4.ModThree π (p ^ f))
    {ψ : K ⧸ aschbacherSolvableCore 3 K ≃* projImage (Sec4.slPi π 3 (p ^ f) Fld)}
    {y₀ : GL (Fin 3) Fld} (hx₀ψ : Ronan138S.ActsPGL ψ x₀ y₀)
    (hy₀3 : Sec4.Type123 π (p ^ f) Fld y₀ 3) : ¬ Sec4.ModNine π (p ^ f) := by
  intro h9
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hπ : π = false → UnitaryFieldData p f Fld := fun h => by subst h; exact hPi.unitary
  have hq' : π = false → Sec4.ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨x, y, t, hfr⟩ := Ronan138S.exists_frame138_t hH hF hPGL
  have hH' := hH
  obtain ⟨h, -, hcE, hE3, -, hEN, -, -, -⟩ := hH'
  have hc3 : c ^ 3 = 1 := hE3.2 c hcE
  have hc1 : c ≠ 1 := h.ne_one
  have hc : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hcF : c ∈ F := hfr.hcF
  have hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := hfr.hEab
  have hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := hfr.hFab
  have heE : e ∈ E := (zpowers_mem_omegaA_iff.mp heΩ).1
  have he3 : e ^ 3 = 1 := hE3.2 e heE
  have he1 : e ≠ 1 := by
    rintro rfl
    exact hec (Subgroup.one_mem _)
  have hXF := Ronan138S.mem_partTwoF_of_hyp138 hH
  have hD : Sec13Data G E e K :=
    { h.toPartTwoStanding with
      partTwoS_eq := h.partTwoS_eq
      mem_partTwoF := hXF.1
      not_mem_partTwoT := hXF.2
      zpowers_mem_omegaA := heΩ
      mem_lA := hK }
  obtain ⟨heK, hautIn, -⟩ :=
    Ronan138S.facts131_of_isZ3PGLThreePi h131 sporadicModels131 hD hPGLK
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hK.1
  haveI : Group.IsPerfect (K ⧸ aschbacherSolvableCore 3 K) := hKq.1
  haveI : Group.IsPerfect (projImage (Sec4.slPi π 3 (p ^ f) Fld)) :=
    Group.IsPerfect.ofSurjective (f := ψ.toMonoidHom) ψ.surjective
  have hCeN : ∀ g : G, g * e = e * g → g ∈ Subgroup.normalizer (K : Set G) := fun g hg =>
    normalizer_zpowers_le_normalizer_of_not_mem h131 sporadicModels131 hD heK
      (mem_normalizer_zpowers_of_commute hg.symm)
  have hCEset := sectionCentralizer_eq_inf hK.2.1
  rw [hK.2.2.1] at hCEset
  have hCE : E ⊓ Sec4.thetaQuotCentralizer K = Subgroup.zpowers e :=
    SetLike.coe_injective hCEset.symm
  have heθ : e ∈ Sec4.thetaQuotCentralizer K :=
    (Subgroup.mem_inf.mp (hCE.symm ▸ Subgroup.mem_zpowers e : e ∈ E ⊓ _)).2
  have hcK : c ∉ Sec4.thetaQuotCentralizer K := by
    intro hcK
    have hce : c ∈ Subgroup.zpowers e := hCE ▸ Subgroup.mem_inf.mpr ⟨hcE, hcK⟩
    apply hec
    rw [Ronan138S.zpowers_eq_of_mem hc3 hc1 he3 he1 hce]
    exact Subgroup.mem_zpowers e
  have hNL := normalizer_zpowers_le_normalizer_L hH hF hPGL hFmax
  have hEFD : E ⊔ F ≤ Subgroup.centralizer ({c} : Set G) ⊓
      Subgroup.centralizer ({e} : Set G) := by
    refine sup_le (fun a ha => ⟨?_, ?_⟩) (fun a ha => ⟨?_, ?_⟩)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hEab a ha c hcE)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hEab a ha e heE)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hFab a ha c hcF)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hFab a ha e heF)
  obtain ⟨P, hPS, hEFP⟩ := exists_isSylowOf_ge hEF3 hEFD
  have hP3 := hPS.isPGroup
  have hPc : P ≤ Subgroup.centralizer ({c} : Set G) := hPS.le.trans inf_le_left
  have hPN : P ≤ Subgroup.normalizer (L : Set G) := fun g hg =>
    hNL (mem_normalizer_zpowers_of_commute
      (Subgroup.mem_centralizer_singleton_iff.mp (hPc hg)).symm)
  have hEP : E ≤ P := le_sup_left.trans hEFP
  have hFP : F ≤ P := le_sup_right.trans hEFP
  obtain ⟨-, horder3⟩ := commute_and_mem_zpowers hH hF hPGL hFmax hP3 hFP hPc hPN
  have hT3 : IsPGroup 3 ↥(P ⊓ Sec4.thetaQuotCentralizer L) := hP3.to_le inf_le_left
  have hTK : ∀ v ∈ P ⊓ Sec4.thetaQuotCentralizer L, v ∈ Sec4.thetaQuotCentralizer K → v = 1 :=
    fun v hvT hvK => eq_one_of_mem_of_pow_three hT3 horder3 hc3 hcK hvT hvK
  have hx₀c : x₀ * c = c * x₀ := hEab x₀ hx₀E c hcE
  have hconjT : ∀ g ∈ P, ∀ v ∈ P ⊓ Sec4.thetaQuotCentralizer L,
      g * v * g⁻¹ ∈ P ⊓ Sec4.thetaQuotCentralizer L := fun g hg v hv =>
    ⟨P.mul_mem (P.mul_mem hg hv.1) (P.inv_mem hg),
      Sec6.conj_mem_thetaQuotCentralizer hv.2 (hPN hg)⟩
  have hTpgl : ∀ v ∈ P ⊓ Sec4.thetaQuotCentralizer L, ∀ M : GL (Fin 3) Fld,
      Ronan138S.ActsPGL ψ v M → v ∈ Subgroup.zpowers c := fun v hv M hvM =>
    mem_zpowers_of_actsPGL hPi hq hx₀ψ hy₀3 hc3 hcK hx₀c (hconjT x₀ (hEP hx₀E)) hTK horder3
      hT3 hv hvM
  have hKact : ∀ k ∈ K, ∃ s ∈ Sec4.slPi π 3 (p ^ f) Fld, Ronan138S.ActsPGL ψ k s := by
    intro k hk
    obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp
      (ψ ((⟨k, hk⟩ : K) : K ⧸ aschbacherSolvableCore 3 K)).2
    exact ⟨s, hs, Ronan138S.actsPGL_of_mem hπ hk hs hse.symm⟩
  have hKT : ∀ v ∈ K, v ∈ P ⊓ Sec4.thetaQuotCentralizer L → v ∈ Subgroup.zpowers c := by
    intro v hvK hvT
    obtain ⟨s, -, hs⟩ := hKact v hvK
    exact hTpgl v hvT s hs
  have hyK : y ∈ Subgroup.normalizer (K : Set G) := hCeN y (hFab y hfr.hyF e heF)
  obtain ⟨k, hkK, a, b, hcab⟩ :=
    Sec4.Ronan148L.exists_mem_mul_pow_of_frame hfr heE heF heL heK hK.2.1 hyK hautIn
  obtain ⟨s, hs, hkψ⟩ := hKact k hkK
  have heψ : Ronan138S.ActsPGL ψ e 1 := Ronan138S.actsPGL_of_mem_thetaQuotCentralizer heθ
  have hcψ : Ronan138S.ActsPGL ψ c (s ^ a) := by
    have := (hkψ.pow hπ a).mul (heψ.pow hπ b)
    rwa [one_pow, mul_one, ← hcab] at this
  have hYsl : s ^ a ∈ Sec4.slPi π 3 (p ^ f) Fld := pow_mem hs a
  have hYH : s ^ a ∈ Sec4.glPi π 3 (p ^ f) Fld := Sec4.slPi_le_glPi hπ hYsl
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hPi hq
  have hYZ : s ^ a ∉ Sec4.zPi π 3 (p ^ f) Fld := by
    intro hz
    rw [Sec4.zPi_eq hπ hq' hτ hτ1] at hz
    exact hcK (hcψ.mem_thetaQuotCentralizer (Sec4.mk_eq_one_iff_mem_statedScalars.mpr hz.2))
  have hY3 : (s ^ a) ^ 3 ∈ Sec4.zPi π 3 (p ^ f) Fld := by
    rw [Sec4.zPi_eq hπ hq' hτ hτ1]
    refine ⟨pow_mem hYH 3, ?_⟩
    have h1 := hcψ.pow hπ 3
    rw [hc3] at h1
    have h2 := Ronan138S.ActsPGL.mk_eq hPi hq h1 (Ronan138S.actsPGL_one hπ)
    rw [map_one] at h2
    exact Sec4.mk_eq_one_iff_mem_statedScalars.mp h2
  have hcomm : y₀ * s ^ a * y₀⁻¹ * (s ^ a)⁻¹ ∈ StatedScalars (Fin 3) Fld := by
    have h1 := Ronan138S.ActsPGL.commute hPi hq hx₀ψ hcψ hx₀c
    rw [← Sec4.mk_eq_one_iff_mem_statedScalars, map_mul, map_mul, map_mul, map_inv, map_inv, h1]
    group
  obtain ⟨-, -, hirr₀⟩ := id hy₀3
  rcases Sec4.type123_exhaust hPi hq hYH hYZ hY3 with h1 | h2 | h3
  rotate_left
  · exact Sec13.not_irreducible_of_commute_type2 hPi hq h2 hcomm hirr₀
  · exact Sec4.not_inner_of_type3 hPi hq hYH h3 ⟨s ^ a, hYsl, fun m _ => rfl⟩
  obtain ⟨τ', hτ', hτ'1, z, hz, g, hg, hD'⟩ := h1
  have hzS := Sec4.mem_statedScalars_of_mem_zPi hPi hq hτ' hτ'1 hz
  have h9d : 9 ∣ Sec4.qSubPi π (p ^ f) :=
    (Sec4.modNine_iff (Nat.one_le_pow _ _ hPi.prime.pos)).mp h9
  obtain ⟨Q, hQ3, hQ81, hQfix⟩ :=
    Ronan138B.exists_fixed_subgroup_eightyOne hPi h9d hτ' hτ'1 hzS hg hD'
  set QK := Q.map ψ.symm.toMonoidHom with hQK
  have hQK3 : IsPGroup 3 QK := hQ3.map _
  have hQK81 : 81 ≤ Nat.card QK := by
    rw [hQK, Subgroup.card_map_of_injective ψ.symm.injective]
    exact hQ81
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := hK.2.1 hcE
  have hQKfix : ∀ q ∈ QK,
      Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨c, hcN⟩) q = q := by
    rintro _ ⟨m, hm, rfl⟩
    apply ψ.injective
    apply Subtype.ext
    obtain ⟨hcN', -, hact⟩ := hcψ
    have h1 := hact (ψ.symm m)
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at h1 ⊢
    rw [h1, hQfix m hm]
  obtain ⟨Q', hQ'le, hQ'3, hQ'card⟩ :=
    Sec4.Ronan148L.exists_pGroup_le_centralizer_of_fixed hcN (k := 1)
      (by rw [pow_one]; exact hc3) QK hQK3 hQKfix
  have hND : K ⊓ Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer ({e} : Set G) :=
    le_inf inf_le_right (inf_le_left.trans (Sec6.le_centralizer_of_mem_thetaComponentsAt hK.1))
  have hDN : Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer ({e} : Set G) ≤
      Subgroup.normalizer ((K ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) := by
    intro g hg
    have hgc : g ∈ Subgroup.centralizer ({c} : Set G) := (Subgroup.mem_inf.mp hg).1
    have hgK : g ∈ Subgroup.normalizer (K : Set G) :=
      hCeN g (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hg).2)
    rw [Subgroup.mem_normalizer_iff]
    intro v
    rw [Subgroup.mem_inf, Subgroup.mem_inf, ← Subgroup.mem_normalizer_iff.mp hgK v]
    constructor
    · rintro ⟨hvK, hvc⟩
      exact ⟨hvK, mul_mem (mul_mem hgc hvc) (inv_mem hgc)⟩
    · rintro ⟨hvK, hvc⟩
      refine ⟨hvK, ?_⟩
      have := mul_mem (mul_mem (inv_mem hgc) hvc) hgc
      rwa [show g⁻¹ * (g * v * g⁻¹) * g = v by group] at this
  have hPNS := hPS.inf_of_le_normalizer hND hDN
  have hPK81 : 81 ≤ Nat.card (P ⊓ K : Subgroup G) := by
    have h1 := card_le_of_isSylowOf hQ'3 hQ'le hPNS
    have h2 : Nat.card (P ⊓ (K ⊓ Subgroup.centralizer ({c} : Set G)) : Subgroup G) ≤
        Nat.card (P ⊓ K : Subgroup G) :=
      Subgroup.card_le_of_le (inf_le_inf_left _ inf_le_left)
    omega
  have hPT := card_le_mul_card_inf hPN hP3 (card_le_27_of_hyp138 hH hPGL)
  have hPKT : P ⊓ K ≤
      Subgroup.normalizer ((P ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · exact hconjT g hg.1 v
    · intro hv
      have := hconjT g⁻¹ (inv_mem hg.1) _ hv
      rwa [show g⁻¹ * (g * v * g⁻¹) * g⁻¹⁻¹ = v by group] at this
  have hcard := Sec6.card_sup_mul_card_inf hPKT
  have hsup : (P ⊓ K) ⊔ (P ⊓ Sec4.thetaQuotCentralizer L) ≤ P := sup_le inf_le_left inf_le_left
  have hsupc := Subgroup.card_le_of_le hsup
  have hinf : (P ⊓ K) ⊓ (P ⊓ Sec4.thetaQuotCentralizer L) ≤ Subgroup.zpowers c :=
    fun v hv => hKT v hv.1.2 hv.2
  have hinfc : Nat.card ((P ⊓ K) ⊓ (P ⊓ Sec4.thetaQuotCentralizer L) : Subgroup G) ≤ 3 := by
    have := Subgroup.card_le_of_le hinf
    rwa [Nat.card_zpowers, hc] at this
  have hTpos : 0 < Nat.card (P ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) := Nat.card_pos
  have hi3 : Nat.card ((P ⊓ K) ⊓ (P ⊓ Sec4.thetaQuotCentralizer L) : Subgroup G) = 3 := by
    by_contra hne
    have hi2 : Nat.card ((P ⊓ K) ⊓ (P ⊓ Sec4.thetaQuotCentralizer L) : Subgroup G) ≤ 2 := by
      omega
    have h1 := Nat.mul_le_mul (hsupc.trans hPT) hi2
    rw [hcard] at h1
    have h2 := Nat.mul_le_mul_right (Nat.card (P ⊓ Sec4.thetaQuotCentralizer L : Subgroup G))
      hPK81
    nlinarith
  have hinfeq : (P ⊓ K) ⊓ (P ⊓ Sec4.thetaQuotCentralizer L) = Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge hinf (by rw [hi3, Nat.card_zpowers, hc])
  have hcK' : c ∈ K :=
    (hinfeq.symm ▸ Subgroup.mem_zpowers c :
      c ∈ (P ⊓ K) ⊓ (P ⊓ Sec4.thetaQuotCentralizer L)).1.2
  have hsupeq : (P ⊓ K) ⊔ (P ⊓ Sec4.thetaQuotCentralizer L) = P := by
    refine Subgroup.eq_of_le_of_card_ge hsup ?_
    have h2 := Nat.mul_le_mul_right (Nat.card (P ⊓ Sec4.thetaQuotCentralizer L : Subgroup G))
      hPK81
    rw [hi3] at hcard
    nlinarith
  have hx₀m : x₀ ∈ ((P ⊓ K : Subgroup G) : Set G) *
      ((P ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hPKT, hsupeq]
    exact hEP hx₀E
  obtain ⟨k₁, hk₁, t₁, ht₁, hkt⟩ := hx₀m
  obtain ⟨s₁, -, hk₁ψ⟩ := hKact k₁ hk₁.2
  have ht₁ψ : Ronan138S.ActsPGL ψ t₁ (s₁⁻¹ * y₀) := by
    have := hk₁ψ.inv.mul hx₀ψ
    rwa [← hkt, inv_mul_cancel_left] at this
  have ht₁K : t₁ ∈ K := Subgroup.zpowers_le.mpr hcK' (hTpgl t₁ ht₁ _ ht₁ψ)
  have hx₀K : x₀ ∈ K := hkt ▸ K.mul_mem hk₁.2 ht₁K
  obtain ⟨s₀, hs₀, hx₀s⟩ := hKact x₀ hx₀K
  have hmk := Ronan138S.ActsPGL.mk_eq hPi hq hx₀ψ hx₀s
  exact Ronan138S.mk_not_mem_projImage_slPi_of_type3 hPi hq hx₀ψ.2.1 hy₀3 ⟨s₀, hs₀, hmk.symm⟩

theorem step138KInndiag_holds (h131 : Item131) : Step138KInndiag := by
  intro G _ _ A c L E hH hPGL F hF hFmax e K heΩ hK heF hec heL hPGLK P hP hEFP _ _ π p f Fld _
    hPi hq ψ w hwN hw _ _
  have hH' := hH
  obtain ⟨h, -, -, -, -, -, -, -, -⟩ := hH'
  have hXF := Ronan138S.mem_partTwoF_of_hyp138 hH
  have hD : Sec13Data G E e K :=
    { h.toPartTwoStanding with
      partTwoS_eq := h.partTwoS_eq
      mem_partTwoF := hXF.1
      not_mem_partTwoT := hXF.2
      zpowers_mem_omegaA := heΩ
      mem_lA := hK }
  obtain ⟨-, -, x₀, hx₀E, hx₀type⟩ :=
    Ronan138S.facts131_of_isZ3PGLThreePi h131 sporadicModels131 hD hPGLK
  obtain ⟨hx₀N, π₀, p₀, f₀, Fld₀, _, hPi₀, hq₀, ψ₀, y₀, hy₀, hy₀3, hx₀act⟩ := hx₀type
  have hx₀ψ : Ronan138S.ActsPGL ψ₀ x₀ y₀ := ⟨hx₀N, hy₀, hx₀act⟩
  have hP3 := CFSG.ABGLocalTools.IsSylowOf.isPGroup hP
  have h9₀ := not_modNine_of_cfg h131 hH hPGL hF hFmax heΩ hK heF hec heL hPGLK
    (hP3.to_le hEFP) hx₀E hPi₀ hq₀ hx₀ψ hy₀3
  have h9 : ¬ Sec4.ModNine π (p ^ f) := fun h9 =>
    h9₀ (Sec13.modNine_of_mulEquiv hPi hq hPi₀ hq₀ ψ ψ₀ h9)
  have h9' : ¬ (p ^ f % 9 = 1 ∨ p ^ f % 9 = 8) := by
    cases π <;> simp only [Sec4.ModNine, Sec4.ModThree, cond_true, cond_false] at h9 hq <;> omega
  have hf3 : ¬ 3 ∣ f := Sec15.Proof158Cartan.not_three_dvd_of_not_modNine hq h9'
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hK.1
  have hq2 : 2 < p ^ f := Item138Proof.two_lt_of_mulEquiv hKq hPi hq ψ
  set ν := Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨w, hwN⟩) with hν
  obtain ⟨k, hk⟩ := hP3 ⟨w, hw.1⟩
  have hwk : w ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hνk : ν ^ 3 ^ k = 1 := by
    rw [hν, ← map_pow, ← map_pow]
    have : (⟨w, hwN⟩ : Subgroup.normalizer (K : Set G)) ^ 3 ^ k = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, hwk, Subgroup.coe_one])
    rw [this, map_one, map_one]
  obtain ⟨y, hy, hconj⟩ := Sec15.Proof158Cartan.inndiag_of_three_pow hPi hq2 hf3
    (MulAut.congr ψ ν) ⟨k, by rw [← map_pow, hνk, map_one]⟩
  refine ⟨y, hy, fun z => ?_⟩
  have h1 := hconj (ψ z)
  have h2 : (MulAut.congr ψ ν) (ψ z) = ψ (ν z) := by
    change ψ (ν (ψ.symm (ψ z))) = ψ (ν z)
    rw [MulEquiv.symm_apply_apply]
  rw [h2] at h1
  exact h1

end Main

end CFSG.RankThree.PartTwo.Sec13.Ronan138V
