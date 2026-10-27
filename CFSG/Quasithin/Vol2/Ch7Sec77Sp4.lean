module

public import CFSG.Quasithin.Vol2.Ch7Sec77Mod
public import CFSG.Quasithin.Vol2.Ch7Sec77LieStmts

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.H.BlkW
  CFSG.Quasithin.SBc17

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem card_map_le_relIndex_mul {K X R : Subgroup G} {Y : Type*} [Group Y] (α : ↥K →* Y)
    (hXK : X ≤ K) (hRX : R ≤ X) :
    Nat.card ((X.subgroupOf K).map α) ≤ R.relIndex X * Nat.card ((R.subgroupOf K).map α) := by
  rw [← Subgroup.relIndex_ker, ← Subgroup.relIndex_ker]
  have h1 := Subgroup.relIndex_inf_mul_relIndex α.ker (R.subgroupOf K) (X.subgroupOf K)
  rw [inf_of_le_left ((fun x hx => hRX hx) : R.subgroupOf K ≤ X.subgroupOf K),
    Subgroup.relIndex_subgroupOf hXK] at h1
  have h0 : (α.ker ⊓ R.subgroupOf K).relIndex (X.subgroupOf K) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have h2 := Subgroup.relIndex_le_of_le_left (inf_le_left : α.ker ⊓ R.subgroupOf K ≤ α.ker) h0
  rw [← h1] at h2
  rw [mul_comm]
  exact h2

namespace Setup

variable (S : Setup T L I)
include S

variable {S} {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)} {θ : G}

namespace MinConf

variable {Vp H : Subgroup G} (C : S.MinConf θ e Vp H)
include C

theorem false_of_sp4Block (hSp4 : Sp4PlaneFixFact) (hF : CharTwo H) {K : Subgroup G}
    (hK : K ∈ cComp H) (h4 : CFSG.Quasithin.IsSp4Block K) {r b : ℕ} (hr : ¬ 3 ∣ r)
    (hyK : θ ^ r ∈ K) (hyb : orderOf (θ ^ r) = 3 ^ b) : False := by
  classical
  have hc := C.conf.hc
  obtain ⟨-, F, hFf, hFt, hF4, α, hαs, hαk, β, hβs, hβk, hβe⟩ := h4
  have hyM : θ ^ r ∈ fsuM T L := (fsuM T L).pow_mem (S.L_le_fsuM hc.mem) r
  have hyo : Odd (orderOf (θ ^ r)) := by rw [hyb]; exact Odd.pow (by decide)
  obtain ⟨hvmU, hvmZ⟩ := C.vm_le_blockU hF hK hyK hyM hyo (pow_not_mem hc hr)
  set X := T ⊓ Subgroup.centralizer (Vp : Set G) ⊓ K with hXdef
  have hXK : X ≤ K := inf_le_right
  have hXS : IsSylowTwoOf X K :=
    CFSG.Quasithin.A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hK) C.conf.sylH
  obtain ⟨R, hRX, hR2, hRQ⟩ := C.exists_index_two_Q (inf_le_left : X ≤ _)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFc : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card, hF4]
  have hcardSp : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) = 979200 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hFc]
    decide
  have hX8 : Nat.card ((X.subgroupOf K).map α) = 2 ^ 8 := by
    rw [card_map_sylow_eq α hαs hXS, hcardSp]
    congr 1
    decide +kernel
  have hR7 : 2 ^ 7 ≤ Nat.card ((R.subgroupOf K).map α) := by
    have h1 := card_map_le_relIndex_mul α hXK hRX
    rw [hX8] at h1
    have h2 : R.relIndex X * Nat.card ((R.subgroupOf K).map α) ≤
        2 * Nat.card ((R.subgroupOf K).map α) := Nat.mul_le_mul_right _ hR2
    omega
  set S₀ : Subgroup ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) := (R.subgroupOf K).map α
    with hS₀
  let W : Submodule F (Fin 2 ⊕ Fin 2 → F) :=
    { carrier := {v | ∀ g ∈ S₀, (((g : ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) :
          GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).mulVec v = v}
      add_mem' := fun {a b} ha hb g hg => by rw [Matrix.mulVec_add, ha g hg, hb g hg]
      zero_mem' := fun g _ => Matrix.mulVec_zero _
      smul_mem' := fun c v hv g hg => by rw [Matrix.mulVec_smul, hv g hg] }
  let f : ↥(S.vm e) → (Fin 2 ⊕ Fin 2 → F) := fun v => Multiplicative.toAdd (β ⟨v, hvmU v.2⟩)
  have hfinj : Function.Injective f := by
    intro v₁ v₂ h
    have h1 : β ⟨v₁, hvmU v₁.2⟩ = β ⟨v₂, hvmU v₂.2⟩ := Multiplicative.toAdd.injective h
    have h2 : (⟨v₁, hvmU v₁.2⟩ : ↥(blockU K)) * (⟨v₂, hvmU v₂.2⟩)⁻¹ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
    rw [hβk, Subgroup.mem_subgroupOf] at h2
    have h3 : (v₁ : G) * (v₂ : G)⁻¹ ∈ S.vm e ⊓ blockZ K :=
      ⟨(S.vm e).mul_mem v₁.2 ((S.vm e).inv_mem v₂.2), h2⟩
    rw [hvmZ, Subgroup.mem_bot, mul_inv_eq_one] at h3
    exact Subtype.ext h3
  have hfW : ∀ v : ↥(S.vm e), f v ∈ W := by
    intro v g hg
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hg
    have hsR : (s : G) ∈ R := Subgroup.mem_subgroupOf.1 hs
    have hsv : ((⟨v, hvmU v.2⟩ : ↥(blockU K)) : G) =
        (s : G) * (⟨v, hvmU v.2⟩ : ↥(blockU K)) * (s : G)⁻¹ := by
      show (v : G) = s * v * (s : G)⁻¹
      rw [← Subgroup.mem_centralizer_iff.mp (hRQ hsR).2 v (vm_le v.2), mul_inv_cancel_right]
    exact (hβe s _ _ hsv).symm
  have h16 : 16 ≤ Nat.card W := by
    have h1 := Nat.card_le_card_of_injective (fun v : ↥(S.vm e) => (⟨f v, hfW v⟩ : ↥W))
      (fun a b hab => hfinj (congrArg (fun z : ↥W => (z : Fin 2 ⊕ Fin 2 → F)) hab))
    rwa [card_vm] at h1
  have hdim : 2 ≤ Module.finrank F W := by
    have h1 : Nat.card W = Nat.card F ^ Module.finrank F W := Module.natCard_eq_pow_finrank
    rw [h1, hFc] at h16
    by_contra hcon
    push Not at hcon
    interval_cases hd : Module.finrank F W <;> simp at h16
  have h64 := hSp4 F hF4 S₀ W hdim fun g hg w hw => hw g hg
  omega

end MinConf

end Setup

end CFSG.Quasithin.H13.Sec77
