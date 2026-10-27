module

public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenDichAct
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenDichInv
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenNum

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.QuasithinUnique.Setup.Campbell
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1511

variable {M V₀ V U S H P Q₀ X : Subgroup G} {p : ℕ} {v : G}

theorem forall_le_qSub15_of_card_X_eq_pow_three
    (c : Cfg1511 M V₀ V U S H P Q₀ p) (hX : XData15 V₀ U H Q₀ p X v)
    (hcard : Nat.card ↥X = p ^ 3) :
    ∀ A ∈ elemFamilyIn 2 (tSub15 M V₀ V U P), A ≤ qSub15 M V₀ V U H P := by
  intro A hA
  haveI : Fact p.Prime := ⟨c.prime⟩
  have hp2 : p ≠ 2 := c.p_ne_two
  haveI : ((iHull15 V₀ U H).subgroupOf Q₀).Normal := c.normal_subgroupOf
  haveI := c.isExtraspecial_quot hX hcard
  have hN3 : Nat.card (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀) = p ^ 3 :=
    (c.card_quot_eq_card_X hX).trans hcard
  haveI : Finite (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀) := inferInstance
  obtain ⟨ρ, hρact, hρker⟩ := c.exists_action_tSub15 hX
  obtain ⟨x, z, g, hH, hCz, -⟩ := hX.heis hcard
  let z' : ↥Q₀ := ⟨z, hX.le hH.z_mem⟩
  have hZ : Subgroup.center (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀) =
      Subgroup.zpowers (QuotientGroup.mk z') :=
    c.center_eq_zpowers_mk hX hcard hH.z_mem (fun y hy => (hH.z_central y hy).symm) hH.z_ne_one
  obtain ⟨hAT, hAcomm, hAsq⟩ := comm_sq_of_mem_elemFamilyIn_two hA
  let ρA : ↥A →* MulAut (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀) :=
    ρ.comp (Subgroup.inclusion hAT)
  have hρA : ∀ a : ↥A, ρA a = ρ ⟨a.1, hAT a.2⟩ := fun a =>
    congrArg ρ (Subtype.ext (by simp [Subgroup.coe_inclusion]))
  have hI : IsElemAbelian 2 (iHull15 V₀ U H) := c.isElemAbelian_iHull15
  have hTN : tSub15 M V₀ V U P ≤ normalizer (iHull15 V₀ U H : Set G) :=
    c.tSub15_le_normalizer_iHull15
  have hvT : v ∈ tSub15 M V₀ V U P := c.V₀_le_tSub15 hX.mem
  have hvv : v * v = 1 := by
    have h2 : v ^ 2 = 1 := c.cex.hyp.elemAbelian₀.2 v hX.mem
    rwa [pow_two] at h2
  let τ : MulAut (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀) := ρ ⟨v, hvT⟩
  have hτne : τ ≠ 1 := by
    intro hτ1
    exact c.not_mem_qSub15 hX (by simpa using hρker ⟨v, hvT⟩ hτ1)
  have hτmul : τ * τ = 1 := by
    have h : (⟨v, hvT⟩ : ↥(tSub15 M V₀ V U P)) * ⟨v, hvT⟩ = 1 := by
      apply Subtype.ext
      simpa using hvv
    change ρ ⟨v, hvT⟩ * ρ ⟨v, hvT⟩ = 1
    rw [← map_mul, h, map_one]
  have hτ2 : ∀ y, τ (τ y) = y := fun y => by
    rw [← MulAut.mul_apply, hτmul, MulAut.one_apply]
  have hτZ : ∀ w ∈ Subgroup.center (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀), τ w = w := by
    intro w hw
    obtain ⟨q', hq'val, hq'mk⟩ := hρact ⟨v, hvT⟩ z'
    have hq'G : (q' : G) = v * z * v⁻¹ := by simpa using hq'val
    have hq'z : q' = z' := by
      apply Subtype.ext
      rw [hq'G]
      show v * z * v⁻¹ = z
      rw [hH.v_comm_z]
      group
    have hτmk : τ (QuotientGroup.mk z') = QuotientGroup.mk z' := by
      have h : ρ ⟨v, hvT⟩ (QuotientGroup.mk z') = QuotientGroup.mk z' := by
        rw [hq'mk, hq'z]
      exact h
    rw [hZ] at hw
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [← hn, map_zpow, hτmk]
  by_cases hall : ∀ a : ↥A,
      ∀ w ∈ Subgroup.center (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀), ρA a w = w
  · have hindex : (ρ.comp (Subgroup.inclusion hAT)).ker.index ≤ 2 :=
      index_ker_le_two_of_isExtraspecial hp2 hN3 ρA hAcomm hAsq hall
    have hI2 := c.card_iHull15_le_mul_card_inf_centralizer hX hA hAT ρ hρker hindex
    by_contra hAQ
    obtain ⟨a, haA, haQ⟩ := SetLike.not_le_iff_exists.mp hAQ
    have haa : a * a = 1 := by
      have h := congrArg (fun y : ↥A => (y : G)) (hAsq ⟨a, haA⟩)
      simpa using h
    let σ : MulAut (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀) := ρ ⟨a, hAT haA⟩
    have hσne : σ ≠ 1 := by
      intro hσ1
      exact haQ (by simpa using hρker ⟨a, hAT haA⟩ hσ1)
    have hσmul : σ * σ = 1 := by
      have h : (⟨a, hAT haA⟩ : ↥(tSub15 M V₀ V U P)) * ⟨a, hAT haA⟩ = 1 := by
        apply Subtype.ext
        simpa using haa
      change ρ ⟨a, hAT haA⟩ * ρ ⟨a, hAT haA⟩ = 1
      rw [← map_mul, h, map_one]
    have hσ2 : ∀ y, σ (σ y) = y := fun y => by
      rw [← MulAut.mul_apply, hσmul, MulAut.one_apply]
    have hσZ : ∀ w ∈ Subgroup.center (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀), σ w = w := by
      intro w hw
      rw [show σ = ρA ⟨a, haA⟩ from (hρA ⟨a, haA⟩).symm]
      exact hall ⟨a, haA⟩ w hw
    have hσ : ∀ y, σ y * y ∈
        Subgroup.center (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀) := by
      rcases mulAut_pm_of_isExtraspecial hp2 hN3 σ hσ2 hσZ with h1 | h1
      · exfalso
        have hσone : σ = 1 :=
          MulEquiv.ext (fun y => mulAut_apply_eq_of_forall_mul_inv_mem_center hp2 σ hσ2 hσZ h1 y)
        exact hσne hσone
      · exact h1
    have hτ : ∀ y, τ y * y ∈
        Subgroup.center (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀) := by
      rcases mulAut_pm_of_isExtraspecial hp2 hN3 τ hτ2 hτZ with h1 | h1
      · exfalso
        have hτone : τ = 1 :=
          MulEquiv.ext (fun y => mulAut_apply_eq_of_forall_mul_inv_mem_center hp2 τ hτ2 hτZ h1 y)
        exact hτne hτone
      · exact h1
    obtain ⟨e, he⟩ := c.isPGroup_two_tSub15 (⟨a, hAT haA⟩ * ⟨v, hvT⟩)
    have hρpow : (σ * τ) ^ (2 ^ e) = 1 := by
      have h := congrArg (fun t : ↥(tSub15 M V₀ V U P) => ρ t) he
      rw [map_pow, map_mul, map_one] at h
      exact h
    have hστ : σ * τ = 1 :=
      mulAut_mul_eq_one_of_neg_neg hp2 σ τ hρpow hσZ hτZ hσ hτ
    have havQρ : ρ (⟨a, hAT haA⟩ * ⟨v, hvT⟩) = 1 := by
      rw [map_mul]
      exact hστ
    have havQ : a * v ∈ qSub15 M V₀ V U H P := by
      have := hρker (⟨a, hAT haA⟩ * ⟨v, hvT⟩) havQρ
      simpa using this
    have havC : a * v ∈ centralizer (iHull15 V₀ U H : Set G) :=
      c.qSub15_le_centralizer_iHull15 hX havQ
    have hleA := inf_centralizer_le_of_mul_mem_centralizer (I := iHull15 V₀ U H)
      (A := A) haA havC
    have hcards := Subgroup.card_le_of_le hleA
    have hfree := card_inf_centralizer_mul_card_commutator_zpowers (I := iHull15 V₀ U H)
      hI (hTN hvT) hvv
    rw [hX.commutator_eq] at hfree
    have h4 := c.four_le_card_v1Sub15 hX hcard
    haveI : Nonempty ↥(iHull15 V₀ U H ⊓ centralizer (A : Set G)) := ⟨1⟩
    have hs : 0 < Nat.card ↥(iHull15 V₀ U H ⊓ centralizer (A : Set G)) := Nat.card_pos
    have h4s : 4 * Nat.card ↥(iHull15 V₀ U H ⊓ centralizer (A : Set G)) ≤
        Nat.card ↥(iHull15 V₀ U H) := by
      calc 4 * Nat.card ↥(iHull15 V₀ U H ⊓ centralizer (A : Set G))
          ≤ Nat.card ↥(v1Sub15 V₀ U) *
              Nat.card ↥(iHull15 V₀ U H ⊓ centralizer (A : Set G)) :=
            Nat.mul_le_mul h4 le_rfl
        _ ≤ Nat.card ↥(v1Sub15 V₀ U) *
              Nat.card ↥(iHull15 V₀ U H ⊓ centralizer ({v} : Set G)) :=
            Nat.mul_le_mul le_rfl hcards
        _ = Nat.card ↥(iHull15 V₀ U H ⊓ centralizer ({v} : Set G)) *
              Nat.card ↥(v1Sub15 V₀ U) := by ring
        _ = Nat.card ↥(iHull15 V₀ U H) := hfree
    omega
  · exfalso
    have hex : ∃ a : ↥A,
        ∃ w ∈ Subgroup.center (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀), ρA a w ≠ w := by
      by_contra hcon
      apply hall
      intro a w hw
      by_contra hne
      exact hcon ⟨a, w, hw, hne⟩
    obtain ⟨a₀, w, hw, hwne⟩ := hex
    let σ₀ : MulAut (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀) := ρA a₀
    have hσ₀mul : σ₀ * σ₀ = 1 := by
      change ρA a₀ * ρA a₀ = 1
      rw [← map_mul, hAsq a₀, map_one]
    have hσ₀2 : ∀ y, σ₀ (σ₀ y) = y := fun y => by
      rw [← MulAut.mul_apply, hσ₀mul, MulAut.one_apply]
    have hinvZ : ∀ w ∈ Subgroup.center (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀),
        σ₀ w = w⁻¹ := by
      rcases mulAut_fix_or_inv_center (p := p) σ₀ hσ₀2 with hfix | hinv
      · exact absurd (hfix w hw) hwne
      · exact hinv
    have hz'center : QuotientGroup.mk z' ∈
        Subgroup.center (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀) := by
      rw [hZ]
      exact Subgroup.mem_zpowers _
    have hσ₀z' : σ₀ (QuotientGroup.mk z') = (QuotientGroup.mk z')⁻¹ := hinvZ _ hz'center
    obtain ⟨q', hq'val, hq'mk⟩ := hρact ⟨a₀.1, hAT a₀.2⟩ z'
    have hq'G : (q' : G) = (a₀ : G) * z * (a₀ : G)⁻¹ := by simpa using hq'val
    have hq'mk' : ρA a₀ (QuotientGroup.mk z') = QuotientGroup.mk q' := by
      rw [hρA a₀]
      exact hq'mk
    have hmk : (QuotientGroup.mk q' : ↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀) =
        QuotientGroup.mk (z'⁻¹) := by
      rw [← hq'mk', hσ₀z']
      simp
    have hmemG : (q' : G)⁻¹ * z⁻¹ ∈ iHull15 V₀ U H := by
      have h := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hmk)
      simpa using h
    have hinv : z * ((a₀ : G) * z * (a₀ : G)⁻¹) ∈ iHull15 V₀ U H := by
      have h : z * (q' : G) ∈ iHull15 V₀ U H := by
        have := (iHull15 V₀ U H).inv_mem hmemG
        simpa [mul_inv_rev, inv_inv] using this
      rwa [hq'G] at h
    have haN : (a₀ : G) ∈ normalizer (iHull15 V₀ U H : Set G) := hTN (hAT a₀.2)
    have hzN : z ∈ normalizer (iHull15 V₀ U H : Set G) :=
      Hyp1510.le_normalizer_iHull15 V₀ U H (hX.le_H c hH.z_mem)
    have ha₀ : (a₀ : G) * (a₀ : G) = 1 := by
      have h := congrArg (fun y : ↥A => (y : G)) (hAsq a₀)
      simpa using h
    have hsqI := card_inf_centralizer_sq_of_inv_mod (I := iHull15 V₀ U H) hI c.prime hp2
      haN hzN ha₀ hH.z_pow hCz hinv
    have hcard_le₀ : Nat.card ↥(iHull15 V₀ U H ⊓ centralizer (A : Set G)) ≤
        Nat.card ↥(iHull15 V₀ U H ⊓ centralizer ({(a₀ : G)} : Set G)) :=
      Subgroup.card_le_of_le (by
        intro y hy
        refine ⟨hy.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact Subgroup.mem_centralizer_iff.mp hy.2 (a₀ : G) a₀.2)
    have hindex4 : (ρ.comp (Subgroup.inclusion hAT)).ker.index ≤ 4 :=
      index_ker_le_four_of_isExtraspecial hp2 hN3 ρA hAcomm hAsq
    have hI4 := c.card_iHull15_le_mul_card_inf_centralizer hX hA hAT ρ hρker hindex4
    haveI : Nonempty ↥(iHull15 V₀ U H ⊓ centralizer ({(a₀ : G)} : Set G)) := ⟨1⟩
    have hs₀pos : 0 < Nat.card ↥(iHull15 V₀ U H ⊓ centralizer ({(a₀ : G)} : Set G)) :=
      Nat.card_pos
    have hI16 : Nat.card ↥(iHull15 V₀ U H) ≤ 16 := by
      have hs₀le : Nat.card ↥(iHull15 V₀ U H ⊓ centralizer ({(a₀ : G)} : Set G)) ≤ 4 := by
        have h : Nat.card ↥(iHull15 V₀ U H ⊓ centralizer ({(a₀ : G)} : Set G)) *
            Nat.card ↥(iHull15 V₀ U H ⊓ centralizer ({(a₀ : G)} : Set G)) ≤
            4 * Nat.card ↥(iHull15 V₀ U H ⊓ centralizer ({(a₀ : G)} : Set G)) := by
          rw [← sq, hsqI]
          exact hI4.trans (Nat.mul_le_mul le_rfl hcard_le₀)
        exact Nat.le_of_mul_le_mul_right h hs₀pos
      calc Nat.card ↥(iHull15 V₀ U H)
          = Nat.card ↥(iHull15 V₀ U H ⊓ centralizer ({(a₀ : G)} : Set G)) ^ 2 :=
            hsqI.symm
        _ = Nat.card ↥(iHull15 V₀ U H ⊓ centralizer ({(a₀ : G)} : Set G)) *
              Nat.card ↥(iHull15 V₀ U H ⊓ centralizer ({(a₀ : G)} : Set G)) := sq _
        _ ≤ 4 * 4 := Nat.mul_le_mul hs₀le hs₀le
        _ = 16 := by norm_num
    obtain ⟨k, hk2, hkcard, -⟩ := c.exists_k hX hcard
    have hp3 : 3 ≤ p := by
      have h2 := c.prime.two_le
      have h3 := hp2
      omega
    have h64 : 64 ≤ Nat.card ↥(iHull15 V₀ U H) := by
      rw [hkcard]
      have h6 : 6 ≤ p * k := by
        simpa using Nat.mul_le_mul hp3 hk2
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (p * k) := Nat.pow_le_pow_right (by norm_num) h6
    omega

end Cfg1511

end CFSG.LocalAnalysis.WeakClosure81
