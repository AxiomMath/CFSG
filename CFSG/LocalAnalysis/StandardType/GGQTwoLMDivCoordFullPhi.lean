module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordFullAux3
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordFullWnorm
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrameLAux

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.UCoord Matrix CFSG.ClassicalInvolution.Phan

variable {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {m : ℕ}
  {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {L0 : Type} [Group L0]
  {c : ↥L →* L0} {π : Su F0 2 1 m →* L0} {ρ : ↥Bs →* MulAut L0}
  {hN : Bs ≤ Subgroup.normalizer (L : Set G)}

theorem qTwoLMDivF_phi_eq_one_iff (hm : 4 ≤ m) (hperf : commutator ↥L = ⊤)
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) (hF0 : Nat.card F0 = 4)
    {δ : (Fin m → Multiplicative (ZMod 3)) →* GL (Fin m) F0} (hδ : QTwoDivFullTorus hF0 δ)
    (b : ↥Bs) : qTwoLMDivF_phi hm hU hF0 hδ b = 1 ↔ ggGamma L hN b = 1 := by
  rw [qTwoLMDivF_phi_apply hm hU hF0 hδ, QuotientGroup.eq_one_iff]
  constructor
  · intro hmem
    obtain ⟨z, hz⟩ := (hδ.scalar _).mpr hmem
    rw [qTwoLMDivF_coord_spec] at hz
    have hρ : ∀ x : L0, ρ b x = x := by
      intro x
      obtain ⟨s, rfl⟩ := hU.π_surj x
      obtain ⟨s', hs', hπ'⟩ := qTwoLMDivF_rep_act hU b s
      have hss : s' = s := Subtype.ext (by rw [hs']; exact qTwoLMDivF_scalar_conj hz _)
      rw [hπ', hss]
    have hAB : (ggGamma L hN b).toMonoidHom = MonoidHom.id ↥L := by
      apply qTwoFrameLP_eq_of_mul_inv_mem_center hperf
      intro l
      apply hU.c_ker
      rw [MonoidHom.mem_ker]
      show c (ggGamma L hN b l * l⁻¹) = 1
      rw [map_mul, map_inv, qTwoLMDivF_c_gamma hU b l, hρ, mul_inv_cancel]
    exact MulEquiv.ext fun l => DFunLike.congr_fun hAB l
  · intro h1
    have hρ : ∀ x : L0, ρ b x = x := by
      intro x
      obtain ⟨l, rfl⟩ := hU.c_surj x
      rw [← qTwoLMDivF_c_gamma hU b l, h1]
      rfl
    have htriv : ∀ s : Su F0 2 1 m, ∃ s' : Su F0 2 1 m,
        (s' : GL (Fin m) F0) = (1 : GL (Fin m) F0) * (s : GL (Fin m) F0) *
          (1 : GL (Fin m) F0)⁻¹ ∧ ρ b (π s) = π s' :=
      fun s => ⟨s, by rw [one_mul, inv_one, mul_one], hρ _⟩
    obtain ⟨z, hz⟩ := qTwoLMDivF_rigid_scalar hm hU htriv (qTwoLMDivF_rep_act hU b)
    refine (hδ.scalar _).mp ⟨z, ?_⟩
    rw [qTwoLMDivF_coord_spec]
    simpa using hz

theorem qTwoLMDivF_phi_surjective (hm : 4 ≤ m) (hperf : commutator ↥L = ⊤)
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) (hF0 : Nat.card F0 = 4)
    {δ : (Fin m → Multiplicative (ZMod 3)) →* GL (Fin m) F0} (hδ : QTwoDivFullTorus hF0 δ)
    {x : G} (hord : orderOf x = 3)
    (hker : ∀ b : ↥Bs, ggGamma L hN b = 1 ↔ (b : G) ∈ Subgroup.zpowers x) (hx : x ∈ Bs)
    (hcard : Nat.card Bs = 3 ^ m) (hQm : Nat.card (QTwoQm m) = 3 ^ (m - 1)) :
    Function.Surjective (qTwoLMDivF_phi hm hU hF0 hδ) := by
  have hker_eq : (qTwoLMDivF_phi hm hU hF0 hδ).ker = Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
    ext b
    rw [MonoidHom.mem_ker, qTwoLMDivF_phi_eq_one_iff hm hperf hU hF0 hδ, hker,
      Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hcardker : Nat.card (qTwoLMDivF_phi hm hU hF0 hδ).ker = 3 := by
    rw [hker_eq, Nat.card_zpowers, Subgroup.orderOf_mk, hord]
  have h := Subgroup.card_ker_mul_card_range (qTwoLMDivF_phi hm hU hF0 hδ)
  rw [hcardker, hcard] at h
  have h3m : 3 ^ m = 3 * 3 ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hr : Nat.card (qTwoLMDivF_phi hm hU hF0 hδ).range = Nat.card (QTwoQm m) := by
    rw [hQm]
    rw [h3m] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  exact MonoidHom.range_eq_top.mp (Subgroup.eq_top_of_card_eq _ hr)

theorem qTwoLMDivF_phi_conj (hm : 4 ≤ m) (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ)
    (hF0 : Nat.card F0 = 4)
    {δ : (Fin m → Multiplicative (ZMod 3)) →* GL (Fin m) F0} (hδ : QTwoDivFullTorus hF0 δ)
    {n : ↥L} {u : Su F0 2 1 m} (hn : c n = π u) (σ : Equiv.Perm (Fin m))
    (hu : ∀ f, (u : GL (Fin m) F0) * δ f * (u : GL (Fin m) F0)⁻¹ =
      δ (SpCoord.permAut σ f)) {b b' : ↥Bs}
    (h : ggGamma L hN b' = MulAut.conj n * ggGamma L hN b * (MulAut.conj n)⁻¹) :
    qTwoLMDivF_phi hm hU hF0 hδ b' =
      QuotientGroup.mk (SpCoord.permAut σ (qTwoLMDivF_coord hU hF0 hδ b)) := by
  obtain ⟨z, hz⟩ := qTwoLMDivF_scalar_of_gamma_eq hm hU hn h
  rw [qTwoLMDivF_phi_apply hm hU hF0 hδ, QuotientGroup.eq_iff_div_mem]
  refine (hδ.scalar _).mp ⟨z, ?_⟩
  have h1 : qTwoLMDivF_rep hU b' = δ (qTwoLMDivF_coord hU hF0 hδ b') :=
    (qTwoLMDivF_coord_spec hU hF0 hδ b').symm
  have h2 : (u : GL (Fin m) F0) * qTwoLMDivF_rep hU b * (u : GL (Fin m) F0)⁻¹ =
      δ (SpCoord.permAut σ (qTwoLMDivF_coord hU hF0 hδ b)) := by
    rw [← qTwoLMDivF_coord_spec hU hF0 hδ b]
    exact hu _
  have h3 : δ (qTwoLMDivF_coord hU hF0 hδ b') *
      (δ (SpCoord.permAut σ (qTwoLMDivF_coord hU hF0 hδ b)))⁻¹ =
      δ (qTwoLMDivF_coord hU hF0 hδ b' /
        SpCoord.permAut σ (qTwoLMDivF_coord hU hF0 hδ b)) := by
    rw [map_div, div_eq_mul_inv]
  rw [← h3, ← h2, ← h1]
  exact hz

@[expose] noncomputable def qTwoLMDivF_theta (hm : 4 ≤ m) (hperf : commutator ↥L = ⊤)
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) (hF0 : Nat.card F0 = 4)
    {δ : (Fin m → Multiplicative (ZMod 3)) →* GL (Fin m) F0} (hδ : QTwoDivFullTorus hF0 δ)
    (hsurj : Function.Surjective (qTwoLMDivF_phi hm hU hF0 hδ)) :
    QTwoQm m ≃* ↥(ggGamma L hN).range :=
  (QuotientGroup.quotientKerEquivOfSurjective (qTwoLMDivF_phi hm hU hF0 hδ) hsurj).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (M := (qTwoLMDivF_phi hm hU hF0 hδ).ker)
      (N := (ggGamma L hN).ker)
      (Subgroup.ext fun b => by
        rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
        exact qTwoLMDivF_phi_eq_one_iff hm hperf hU hF0 hδ b)).trans
      (QuotientGroup.quotientKerEquivRange (ggGamma L hN)))

theorem qTwoLMDivF_theta_phi (hm : 4 ≤ m) (hperf : commutator ↥L = ⊤)
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) (hF0 : Nat.card F0 = 4)
    {δ : (Fin m → Multiplicative (ZMod 3)) →* GL (Fin m) F0} (hδ : QTwoDivFullTorus hF0 δ)
    (hsurj : Function.Surjective (qTwoLMDivF_phi hm hU hF0 hδ)) (b : ↥Bs) :
    qTwoLMDivF_theta hm hperf hU hF0 hδ hsurj (qTwoLMDivF_phi hm hU hF0 hδ b) =
      ⟨ggGamma L hN b, b, rfl⟩ := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective (qTwoLMDivF_phi hm hU hF0 hδ) hsurj)
      (QuotientGroup.mk b) = qTwoLMDivF_phi hm hU hF0 hδ b := rfl
  unfold qTwoLMDivF_theta
  rw [MulEquiv.trans_apply, ← h1, MulEquiv.symm_apply_apply, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

end CFSG.StandardType.QTwo

end
