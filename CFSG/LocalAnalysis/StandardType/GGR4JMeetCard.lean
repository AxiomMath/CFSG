module

public import CFSG.LocalAnalysis.StandardType.GGR4JCardDefs
public import CFSG.LocalAnalysis.StandardType.GGR4Lemma47c
public import CFSG.LocalAnalysis.StandardType.GGR4AutInn
public import CFSG.LocalAnalysis.StandardType.GGKGASp
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveInnAll

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

theorem ggAutomizer_card_eq_of_torusSCRank_p
    {G : Type} [Group G] [Finite G] {Bs J : Subgroup G}
    {R : Type} [Group R] {I : Set (MulAut R)} {N p r : ℕ} [Fact p.Prime] (hr : 3 ≤ r)
    (θ : (↥J ⧸ Subgroup.center ↥J) ≃* R) (hInnI : LargeEvenInnSet R ⊆ I)
    (hSCRank : GGTorusSCRank p r R I) (hAut : GGTorusAutCardSC p R I r N)
    (hBsEA : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hJperf : commutator ↥J = ⊤) (hZ : ∀ g ∈ Subgroup.center ↥J, Nat.Coprime p (orderOf g))
    (hInn : ∀ b ∈ Bs, ∃ k ∈ J, ∀ l ∈ J, b * l * b⁻¹ = k * l * k⁻¹) :
    Nat.card (ggAutomizer J Bs) = N := by
  obtain ⟨-, -, hself, -, hcard_aut⟩ := ggLemma47c hBsEA hSC hZ hInn
  have hBXea : IsElemAbelian p (Bs ⊓ J) := CFSG.Open.IsElemAbelian.mono hBsEA inf_le_left
  let A : Subgroup (MulAut ↥J) :=
    Subgroup.map (MulAut.conj : ↥J →* MulAut ↥J) ((Bs ⊓ J).subgroupOf J)
  have hAabel : IsElemAbelian p A := by
    have hc : ∀ a b : ↥((Bs ⊓ J).subgroupOf J), a * b = b * a := fun a b =>
      Subtype.ext (by
        apply Subtype.ext
        simpa using CFSG.Open.IsElemAbelian.comm hBXea (Subgroup.mem_subgroupOf.mp a.2)
          (Subgroup.mem_subgroupOf.mp b.2))
    have hpow : ∀ a : ↥((Bs ⊓ J).subgroupOf J), a ^ p = 1 := fun a =>
      Subtype.ext (by
        apply Subtype.ext
        simpa using hBXea.2 ((a : ↥J) : G) (Subgroup.mem_subgroupOf.mp a.2))
    have h := isElemAbelian_range hc hpow
      (MulAut.conj.comp ((Bs ⊓ J).subgroupOf J).subtype)
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at h
  have hAself : GGTorusSelfCent p A := by
    intro n hn hnp
    have hnC : (n : G) ∈ Subgroup.centralizer ((Bs ⊓ J : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have hcJ : c ∈ J := (Subgroup.mem_inf.mp hc).2
      have hcn : (MulAut.conj ⟨c, hcJ⟩ : MulAut ↥J) n = n :=
        hn _ (Subgroup.mem_map.mpr ⟨⟨c, hcJ⟩, Subgroup.mem_subgroupOf.mpr hc, rfl⟩)
      have h2 : c * (n : G) * c⁻¹ = (n : G) := by
        have h := congrArg (fun u : ↥J => (u : G)) hcn
        simpa only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] using h
      calc c * (n : G) = (c * n * c⁻¹) * c := by group
        _ = (n : G) * c := by rw [h2]
    have hnp' : (n : G) ^ p = 1 := by
      have h := congrArg (fun u : ↥J => (u : G)) hnp
      simpa using h
    have hnBJ : (n : G) ∈ Bs ⊓ J := hself (n : G) n.2 hnC hnp'
    exact Subgroup.mem_map.mpr ⟨n, Subgroup.mem_subgroupOf.mpr hnBJ, rfl⟩
  have hcardinn : Nat.card ↥(ggAutomizer J (Bs ⊓ J)) =
      Nat.card ↥(ggAutomizer (MulAut.conj : ↥J →* MulAut ↥J).range A) :=
    ggAutomizer_card_eq_inn inf_le_right hBXea hZ
  have hcardAutEq : Nat.card ↥(ggAutomizer J Bs) =
      Nat.card ↥(ggAutomizer (MulAut.conj : ↥J →* MulAut ↥J).range A) :=
    hcard_aut.trans hcardinn
  let ψ : ↥J →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥J))
  have hsurj : Function.Surjective ψ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center ↥J))
  have hker : ψ.ker ≤ Subgroup.center ↥J := by
    have hker_eq : ψ.ker = Subgroup.center ↥J := by
      dsimp [ψ]
      rw [← MonoidHom.comap_ker]
      rw [MonoidHom.ker_eq_bot (θ : ↥J ⧸ Subgroup.center ↥J →* R) (MulEquiv.injective θ)]
      rw [MonoidHom.comap_bot]
      exact QuotientGroup.ker_mk' _
    rw [hker_eq]
  have hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : ↥J, φ (ψ l) = ψ (a l) := by
    intro a ha
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp ha
    refine ⟨MulAut.conj (θ (QuotientGroup.mk k)), hInnI (Set.mem_range_self _), ?_⟩
    intro l
    change MulAut.conj (θ (QuotientGroup.mk k)) (θ (QuotientGroup.mk l)) =
      θ (QuotientGroup.mk ((MulAut.conj k) l))
    rw [MulAut.conj_apply, MulAut.conj_apply]
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
  have hpA : p ^ r ≤ Nat.card ↥A :=
    hSCRank ↥J ψ hsurj hker hJperf A hAabel hAI hAself
  have hp3A : p ^ 3 ≤ Nat.card ↥A :=
    (Nat.pow_le_pow_right (Fact.out : p.Prime).pos hr).trans hpA
  have hcardA := (hAut ↥J ψ hsurj hker hJperf A hAabel hAI hp3A hAself).2
  exact hcardAutEq.trans hcardA

theorem ggAutomizer_card_eq_of_torusSCRank
    {G : Type} [Group G] [Finite G] {Bs J : Subgroup G}
    {R : Type} [Group R] {I : Set (MulAut R)} {N : ℕ}
    (θ : (↥J ⧸ Subgroup.center ↥J) ≃* R) (hInnI : LargeEvenInnSet R ⊆ I)
    (hSCRank : GGTorusSCRank 3 3 R I) (hAut : GGTorusAutCardSC 3 R I 3 N)
    (hBsEA : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hJperf : commutator ↥J = ⊤) (hZ : ∀ g ∈ Subgroup.center ↥J, Nat.Coprime 3 (orderOf g))
    (hInn : ∀ b ∈ Bs, ∃ k ∈ J, ∀ l ∈ J, b * l * b⁻¹ = k * l * k⁻¹) :
    Nat.card (ggAutomizer J Bs) = N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ggAutomizer_card_eq_of_torusSCRank_p (p := 3) (r := 3) (by norm_num)
    θ hInnI hSCRank hAut hBsEA hSC hJperf hZ hInn

theorem ggR4J_card_ge_c3
    {G : Type} [Group G] [Finite G] {Bs J : Subgroup G} {f : ℕ}
    (hBsEA : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hJperf : commutator ↥J = ⊤) (hZ : ∀ g ∈ Subgroup.center ↥J, Nat.Coprime 3 (orderOf g))
    (hInn : ∀ b ∈ Bs, ∃ k ∈ J, ∀ l ∈ J, b * l * b⁻¹ = k * l * k⁻¹)
    (hC3 : GGHasLabel ⟨.C, 3, f⟩ (↥J ⧸ Subgroup.center ↥J)) :
    48 ≤ Nat.card (ggAutomizer J Bs) := by
  have hpq : 3 ∣ (2 ^ f) ^ 2 - 1 := by
    have h4 : (2 ^ f) ^ 2 = 4 ^ f := by
      rw [← pow_mul, show f * 2 = 2 * f by omega, pow_mul]
      norm_num
    rw [h4]
    simpa using Nat.sub_dvd_pow_sub_pow 4 1 f
  have hC3' : LargeEvenRawDatum ⟨.C, 3, f⟩
      (fun R _ I F => Nonempty (↥J ⧸ Subgroup.center ↥J ≃* R) ∧ LargeEvenInnSet R ⊆ I) :=
    largeEvenRawDatum_inn_all hC3
  have hraw := (largeEvenLabelAll_and
    (KGA.kga_torusSCRank_label (N := 3) Nat.prime_three (by norm_num) (by norm_num) hpq)
    (KGA.kga_label (N := 3) Nat.prime_three (by norm_num) (by norm_num) hpq)) _ hC3'
  obtain ⟨R, instR, I, F, ⟨⟨⟨θ⟩, hInnI⟩, hSCRank, hAut⟩⟩ := largeEvenRawDatum_exists hraw
  have hcard := ggAutomizer_card_eq_of_torusSCRank θ hInnI hSCRank hAut
    hBsEA hSC hJperf hZ hInn
  have h48 : Nat.card (ggAutomizer J Bs) = 48 := by
    simpa [Nat.factorial] using hcard
  exact h48.ge

end CFSG.StandardType

end
