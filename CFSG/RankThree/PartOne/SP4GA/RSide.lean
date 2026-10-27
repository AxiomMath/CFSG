module

public import CFSG.RankThree.PartOne.K1214.Omega
public import CFSG.RankThree.PartOne.S11d.Facts11
public import CFSG.RankThree.PartOne.S11d.Common
import CFSG.RankThree.PartOne.S12.Sec12Three

public section

namespace CFSG.RankThree.PartOne.SP4GA

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.GroupTheory CFSG.Blueprint
open CFSG.RankThree.PartOne.K1214
open CFSG.RankThree.PartOne.S12K (LieRigidity3)

theorem card_fin_pi_zmod (n r : ℕ) [NeZero n] :
    Nat.card (Fin r → Multiplicative (ZMod n)) = n ^ r := by
  have h : Nat.card (Multiplicative (ZMod n)) = n := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod n) ≃ ZMod n)]
    exact Nat.card_zmod n
  rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, h]

theorem card_le_of_sylowShape {p r e : ℕ} (hp : p.Prime) {Γ : Type*} [Group Γ] [Finite Γ]
    (hZ : ¬ p ∣ Nat.card (Subgroup.center Γ))
    (hS : SylowShape p r e (Γ ⧸ Subgroup.center Γ)) {T : Subgroup Γ} (hT : IsPGroup p ↥T) :
    Nat.card ↥T ≤ p ^ (e * r) := by
  have : Fact p.Prime := ⟨hp⟩
  set π : Γ →* Γ ⧸ Subgroup.center Γ := QuotientGroup.mk' _ with hπ
  have hT' : IsPGroup p ↥(T.map π) := hT.map π
  obtain ⟨S, hS'⟩ := hT'.exists_le_sylow
  have h1 : IsPGroup p ↥(S : Subgroup (Γ ⧸ Subgroup.center Γ)) := S.isPGroup'
  have h2 : ¬ p ∣ (S : Subgroup (Γ ⧸ Subgroup.center Γ)).index := S.not_dvd_index
  have hφ : Nonempty (↥(S : Subgroup (Γ ⧸ Subgroup.center Γ)) ≃*
      (Fin r → Multiplicative (ZMod (p ^ e)))) := hS (S : Subgroup (Γ ⧸ Subgroup.center Γ)) h1 h2
  obtain ⟨φ⟩ := hφ
  have hcardS : Nat.card ↥(S : Subgroup (Γ ⧸ Subgroup.center Γ)) = p ^ (e * r) := by
    have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
    rw [Nat.card_congr φ.toEquiv, card_fin_pi_zmod, ← pow_mul]
  have hker : T ⊓ Subgroup.center Γ = ⊥ :=
    eq_bot_of_pGroup_le (p := p) (hT.to_inf_left) inf_le_right hZ
  refine (Nat.card_le_card_of_injective
    (fun t : ↥T => (⟨π t, hS' (Subgroup.mem_map_of_mem π t.2)⟩ :
      ↥(S : Subgroup (Γ ⧸ Subgroup.center Γ)))) ?_).trans
    hcardS.le
  intro t₁ t₂ h
  have h1 : π t₁ = π t₂ := congrArg Subtype.val h
  have h2 : (t₁ : Γ)⁻¹ * t₂ ∈ Subgroup.center Γ := QuotientGroup.eq.mp h1
  have h3 : (t₁ : Γ)⁻¹ * t₂ ∈ T := T.mul_mem (T.inv_mem t₁.2) t₂.2
  have h4 : (t₁ : Γ)⁻¹ * t₂ ∈ T ⊓ Subgroup.center Γ := ⟨h3, h2⟩
  rw [hker, Subgroup.mem_bot] at h4
  exact Subtype.ext (inv_mul_eq_one.mp h4)

section Main

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {b : G} {K I X P Q : Subgroup G}

theorem c_not_centralize_R
    (h112 : InSec11Two) (hRig : LieRigidity3) (hKR : KFixedRes) (hFix : FieldFixedPElements)
    (ctx : Fus12Ctx G p A c L E) (hL : Layer1212 p A c L E b K I)
    (hC : Choice1212 p E b I X P Q) (hF : Field1213 p A c L b K I) :
    ∃ r ∈ P ⊓ I, c * r ≠ r * c := by
  classical
  obtain ⟨hp, hp5⟩ := prime_five_le ctx
  have : Fact p.Prime := ⟨hp⟩
  have hKR' := hKR G p A c L E ctx b K I X P Q hL hC hF
  obtain ⟨r, e, hr, he2, hEcard, hIsh, hKsh⟩ := rData hRig ctx hL hF hKR'
  have hRs := R_sylow ctx hL hC
  have hZI := zI_pPrime h112 ctx hL hF
  have hRp : IsPGroup p ↥((P ⊓ I).subgroupOf I) :=
    hRs.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hRs.1).symm
  obtain ⟨φ⟩ := SylowShape.exists_equiv hp (Subgroup.center ↥I) hZI hIsh hRp hRs.2.2
  have hRcard : Nat.card ↥(P ⊓ I) = p ^ (e * r) := by
    have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
    rw [Nat.card_congr ((Subgroup.subgroupOfEquivOfLe hRs.1).symm.trans φ).toEquiv,
      card_fin_pi_zmod, ← pow_mul]
  by_contra hcon
  push Not at hcon
  have hPp : IsPGroup p ↥P := P_isPGroup hC
  have h := ctx.hyp
  have hAel := h.A_elem
  obtain ⟨hbA, -, hb1⟩ := hL.b_mem
  have hEven : EvenLieType (↥I ⧸ Subgroup.center ↥I) :=
    (h112 G p A h.setup b hbA hb1 I ⟨⟨hF.star0.1, hF.two⟩, hF.star0.2⟩).1
  have hq : CFSG.IsQuasisimple ↥I := S11d.isQuasisimple_of_evenLie (I_perfect hL) hEven
  have hset : FieldAutSetting p I c :=
    ⟨hp, hp5, hq, hEven,
      (Sec9A.evenRank_subgroup_le (I ⊔ Subgroup.zpowers c)).trans h.evenRank_eq.le, hZI,
      hF.field⟩
  have hcp : c ^ p = 1 := Sec12Three.pow_eq_one_of_mem_E h (c_mem_E ctx)
  have hbp : b ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) b hbA
  have hbC : b ∈ Subgroup.centralizer (I : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro i hi
    exact Subgroup.mem_centralizer_singleton_iff.1 (I_le_centralizer hL hi)
  have hcb : c * b = b * c := by
    have := hAel.is_comm.comm ⟨c, h.c_mem⟩ ⟨b, hbA⟩
    exact congrArg Subtype.val this
  have hrank : FieldAutRank p I c := ⟨h.evenRank_eq.le, b, hbC, hb1, hbp, hcb⟩
  have hRK : P ⊓ I ≤ P ⊓ K := by
    intro g hg
    refine Subgroup.mem_inf.2 ⟨hg.1, ?_⟩
    have hgI : g ∈ I ⊓ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.mem_inf.2 ⟨hg.2, Subgroup.mem_centralizer_singleton_iff.2 (hcon g hg).symm⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hPp) ⟨g, hg.1⟩
    have hord : ∃ k : ℕ, orderOf g = p ^ k :=
      ⟨k, (Subgroup.orderOf_coe (⟨g, hg.1⟩ : ↥P)).trans hk⟩
    have := hFix G p I c hset hcp hrank g hgI hord
    rwa [← hKR'] at this
  have hPK : IsPGroup p ↥((P ⊓ K).subgroupOf K) :=
    (hPp.to_inf_left (K := K)).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hcardK := card_le_of_sylowShape hp hL.K_center hKsh hPK
  have hcardK' : Nat.card ↥(P ⊓ K) ≤ p ^ ((e - 1) * r) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : P ⊓ K ≤ K)).toEquiv] at hcardK
  have hle := Subgroup.card_le_of_le hRK
  rw [hRcard] at hle
  have hle2 : p ^ (e * r) ≤ p ^ ((e - 1) * r) := hle.trans hcardK'
  have h3 := (Nat.pow_le_pow_iff_right hp.one_lt).1 hle2
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  have hr1 : 1 ≤ r := by omega
  simp only [Nat.add_sub_cancel] at h3
  nlinarith

end Main

end CFSG.RankThree.PartOne.SP4GA
