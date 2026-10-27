module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBPosition

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def GGTorusGenTableB (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (M : Type) [Group M] [Finite M] (L' E E₁ D' J' : Subgroup M) (d : M)
    (θ : L' ⧸ Subgroup.center L' ≃* R) (hE : E ≤ Subgroup.normalizer (L' : Set M)),
    GGTableBPosition p L' E I θ hE → E ⊓ Subgroup.centralizer (L' : Set M) ≠ ⊥ → E₁ ≤ E →
    E₁ ⊓ Subgroup.centralizer (L' : Set M) = ⊥ → Nat.card E = p * Nat.card E₁ →
    Subgroup.normalizer (E : Set M) ≤ Subgroup.normalizer (E₁ : Set M) →
    D' ≤ E → E ⊓ Subgroup.centralizer (L' : Set M) ≤ D' → D' ⊓ E₁ = zpowers d → d ≠ 1 →
    IsComponentOf J' (L' ⊓ Subgroup.centralizer (D' : Set M)) →
    (∀ z ∈ L' ⊓ Subgroup.centralizer (L' : Set M), z ^ p = 1 →
        z ∈ Subgroup.centralizer (E : Set M)) ∧
      ∀ c ∈ L' ⊓ Subgroup.centralizer (E₁ : Set M), (∃ k : ℕ, c ^ p ^ k = 1) →
        (c ∈ Subgroup.centralizer (L' : Set M) ∨
          ¬ p ∣ Nat.card (L' ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M)) →
        ∃ (S : Subgroup M) (W : Set M), IsPGroup p S ∧
          S ≤ Subgroup.centralizer (E₁ : Set M) ∧ S ≤ J' ∧
          W ⊆ Subgroup.normalizer (E₁ : Set M) ∧
          c ∈ Subgroup.closure (⋃ n ∈ W, (fun s => n * s * n⁻¹) '' (S : Set M))

theorem torusWeylCent_at_of_tableB (hF : GGL48NbrFieldInput) {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁) (hJK : J ≤ K) (hUK : U ⊓ K ≤ U₁)
    {R : Type} [Group R] {I : Set (MulAut R)} (θ : L ⧸ Subgroup.center L ≃* R)
    (hL : commutator L = ⊤) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hKG : GGTorusGenTableB p R I) :
    ¬ p ∣ Nat.card (L ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) ∧
    ∀ c ∈ L ⊓ Subgroup.centralizer
        ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G),
      (∃ k : ℕ, c ^ p ^ k = 1) →
      ∃ (S : Subgroup G) (W : Set G), IsPGroup p S ∧
        S ≤ Subgroup.centralizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) ∧
        S ≤ J ∧
        W ⊆ Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) ∧
        c ∈ Subgroup.closure (⋃ n ∈ W, (fun s => n * s * n⁻¹) '' (S : Set G)) := by
  have hp : p.Prime := hS.1.1.1.2.2.2.2.2.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hsS := hS.1.1.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hsS.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hsS.2.2.2.1.1
  have hcycL : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S →
      IsCyclic S := hsS.2.2.2.2
  have hBst := hS.1.1.2.1
  have hBsp : ∀ b ∈ Bs, b ^ p = 1 := hBst.2.1.2
  have hxBs : x ∈ Bs := hBst.1 hsS.2.1
  have hxo : orderOf x = p := orderOf_eq_prime (hBsp x hxBs) hx1
  have hBcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBst.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have h43 := hS.2.2.1
  have h44 := hS.2.2.2.2.2.1
  have hpre := hS.1.1.2.2.1
  set B₁ := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁
  have hxC : x ∈ Subgroup.centralizer (L : Set G) :=
    mem_centralizer_iff.mpr fun l hl => mem_centralizer_singleton_iff.mp (hLx hl)
  have hTp : IsPGroup p ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) := fun t =>
    ⟨1, Subtype.ext (by simpa using hBsp _ t.2.1)⟩
  have hCx : Bs ⊓ Subgroup.centralizer (L : Set G) = zpowers x :=
    le_antisymm (GGL48TW.Cent.le_zpowers_of_isCyclic hp (hcycL _ inf_le_right hTp)
      (fun t ht => hBsp t ht.1) ⟨hxBs, hxC⟩ hx1) (zpowers_le.mpr ⟨hxBs, hxC⟩)
  have hB₁C : B₁ ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    have hbx : b ∈ zpowers x := hCx ▸ (⟨hb.1.1, hb.2⟩ : b ∈ Bs ⊓ Subgroup.centralizer (L : Set G))
    exact Subgroup.mem_bot.mpr (GGL48TW.Cent.eq_one_of_mem_zpowers hp hxo h43.1 hbx hb.1)
  have hDBs : D ≤ Bs := hpre.1.trans hBst.1
  have hxD : x ∈ D := hpre.2.2.2.1
  have hCD : Bs ⊓ Subgroup.centralizer (L : Set G) ≤ D := by
    rw [hCx]; exact zpowers_le.mpr hxD
  have hJc : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) := hpre.2.2.2.2.2.1
  obtain ⟨hza, hc⟩ := hKG G L Bs B₁ D J d θ hBsN (tableBPosition_of_setup hS θ hL hBsN h3)
    (by rw [hCx]; exact Subgroup.zpowers_ne_bot.mpr hx1) inf_le_left hB₁C
    (by rw [card_bstar_eq hS, mul_comm])
    (normalizer_le_normalizer_of_ggFieldCase hS.1) hDBs hCD h44.1
    h44.2.1 hJc
  have hxB₁ : x ∈ Subgroup.centralizer (B₁ : Set G) :=
    mem_centralizer_iff.mpr fun b hb => hBcomm b hb.1 x hxBs
  have hxL : x ∉ L := by
    intro hxL
    obtain ⟨S, W, hSp, hSC, hSJ, hWN, hcl⟩ :=
      hc x ⟨hxL, hxB₁⟩ ⟨1, by rw [pow_one]; exact hBsp x hxBs⟩ (Or.inl hxC)
    exact not_mem_closure_weyl hF hS hUK hSp hSC (hSJ.trans hJK) hWN hcl
  have hZ : ¬ p ∣ Nat.card (L ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) := by
    intro hdvd
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hzo : orderOf (z : G) = p := by rw [Subgroup.orderOf_coe]; exact hz
    have hzp : (z : G) ^ p = 1 := by rw [← hzo]; exact pow_orderOf_eq_one _
    have hzBs : (z : G) ∈ Bs := hBst.2.2.2 _ (hza _ z.2 hzp) hzp
    have hzx : (z : G) ∈ zpowers x := hCx ▸ (⟨hzBs, z.2.2⟩ : (z : G) ∈ Bs ⊓ _)
    have heq : zpowers (z : G) = zpowers x := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hzx)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hzo, hxo])
    have hxz : x ∈ zpowers (z : G) := heq ▸ mem_zpowers x
    exact hxL ((zpowers_le.mpr z.2.1) hxz)
  exact ⟨hZ, fun c hcm hcp => hc c hcm hcp (Or.inr hZ)⟩

end CFSG.StandardType
