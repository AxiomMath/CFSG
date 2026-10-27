module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGR4JNCDefs
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetCard

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

private theorem ncd_one_le_of_card {K : Type} [Field K] [Finite K] {n : ℕ}
    (h : Nat.card K = 2 ^ n) : 1 ≤ n := by
  by_contra hn
  have hn0 : n = 0 := by omega
  subst hn0
  have h2 : 2 ≤ Nat.card K := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    omega
  rw [h] at h2
  norm_num at h2

private theorem ncd_one_le_of_hasLabel_A {f : ℕ} {R : Type} [Group R]
    (h : GGHasLabel ⟨.A, 5, f⟩ R) : 1 ≤ f := by
  obtain ⟨K, hK, hKfin, hKcard, -⟩ := h
  haveI := hK
  haveI := hKfin
  exact ncd_one_le_of_card hKcard

private theorem ncd_one_le_of_hasLabel_twA {f : ℕ} {R : Type} [Group R]
    (h : GGHasLabel ⟨.twA, 5, f⟩ R) : 1 ≤ f := by
  obtain ⟨K, hK, hKfin, hKcard, -⟩ := h
  haveI := hK
  haveI := hKfin
  have h2 : 1 ≤ 2 * f := by
    apply ncd_one_le_of_card (K := K) (n := 2 * f)
    rw [← pow_mul] at hKcard
    rw [Nat.mul_comm f 2] at hKcard
    exact hKcard
  omega

private theorem ncd_one_le_of_hasLabel_twD {f : ℕ} {R : Type} [Group R]
    (h : GGHasLabel ⟨.twD, 4, f⟩ R) : 1 ≤ f := by
  unfold GGHasLabel at h
  rw [show CFSG.StandardType.LargeEvenRawDatum ⟨.twD, 4, f⟩ =
      LargeEvenRecipeOmegaMinus 3 (2 ^ f) from rfl] at h
  unfold LargeEvenRecipeOmegaMinus at h
  obtain ⟨K, hK, hKfin, hKcard, -⟩ := h
  haveI := hK
  haveI := hKfin
  exact ncd_one_le_of_card hKcard

private theorem ncd_core {G : Type} [Group G] [Finite G] {Bs J : Subgroup G}
    {R : Type} [Group R] {I : Set (MulAut R)}
    (θ : (↥J ⧸ Subgroup.center ↥J) ≃* R) (hInnI : LargeEvenInnSet R ⊆ I)
    (hrank : GGTorusAutCardSC 3 R I 3 48)
    (hBsEA : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hJperf : commutator ↥J = ⊤) (hZ : ∀ g ∈ Subgroup.center ↥J, Nat.Coprime 3 (orderOf g))
    (hInn : ∀ b ∈ Bs, ∃ k ∈ J, ∀ l ∈ J, b * l * b⁻¹ = k * l * k⁻¹)
    (hE : 3 ^ 3 ≤ Nat.card (Bs ⊓ J : Subgroup G)) :
    48 ≤ Nat.card (ggAutomizer J Bs) := by
  obtain ⟨-, -, hself, -, hcard_aut⟩ := ggLemma47c hBsEA hSC hZ hInn
  have hBXea : IsElemAbelian 3 (Bs ⊓ J) := isElemAbelian_mono hBsEA inf_le_left
  let A : Subgroup (MulAut ↥J) :=
    Subgroup.map (MulAut.conj : ↥J →* MulAut ↥J) ((Bs ⊓ J).subgroupOf J)
  have hAker : (MulAut.conj.comp ((Bs ⊓ J).subgroupOf J).subtype).ker = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    rw [MonoidHom.mem_ker] at hk
    have hkcenter : (k : ↥J) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro u
      have h2 : (k : ↥J) * u * (k : ↥J)⁻¹ = u := by
        have h := congrArg (fun f : MulAut ↥J => f u) hk
        change (MulAut.conj (k : ↥J)) u = (1 : MulAut ↥J) u at h
        rwa [MulAut.conj_apply, MulAut.one_apply] at h
      have h3 : (k : ↥J) * u = u * (k : ↥J) := by
        calc (k : ↥J) * u = ((k : ↥J) * u * (k : ↥J)⁻¹) * (k : ↥J) := by group
          _ = u * (k : ↥J) := by rw [h2]
      exact h3.symm
    have hmem : (k : ↥J) ∈ (Bs ⊓ J).subgroupOf J ⊓ Subgroup.center ↥J := ⟨k.2, hkcenter⟩
    have hbot : (Bs ⊓ J).subgroupOf J ⊓ Subgroup.center ↥J = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_bot]
      have hyBJ : (y : G) ∈ Bs ⊓ J := Subgroup.mem_subgroupOf.mp hy.1
      have hyp : y ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hBXea.2 (y : G) hyBJ)
      have hcop : Nat.Coprime 3 (orderOf y) := hZ y hy.2
      exact orderOf_eq_one_iff.mp (hcop.symm.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hyp))
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hmem))
  have hBXcard : Nat.card ↥A = Nat.card ↥(Bs ⊓ J) := by
    have hf := card_range_mul_card_ker (MulAut.conj.comp ((Bs ⊓ J).subgroupOf J).subtype)
    rw [hAker, Subgroup.card_bot, mul_one] at hf
    have hrange : (MulAut.conj.comp ((Bs ⊓ J).subgroupOf J).subtype).range = A := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hrange] at hf
    rw [hf]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hAabel : IsElemAbelian 3 A := by
    have hc : ∀ a b : ↥((Bs ⊓ J).subgroupOf J), a * b = b * a := fun a b =>
      Subtype.ext (by
        apply Subtype.ext
        simpa using IsElemAbelian.comm hBXea (Subgroup.mem_subgroupOf.mp a.2)
          (Subgroup.mem_subgroupOf.mp b.2))
    have hpow : ∀ a : ↥((Bs ⊓ J).subgroupOf J), a ^ 3 = 1 := fun a =>
      Subtype.ext (by
        apply Subtype.ext
        simpa using hBXea.2 ((a : ↥J) : G) (Subgroup.mem_subgroupOf.mp a.2))
    have h := isElemAbelian_range hc hpow
      (MulAut.conj.comp ((Bs ⊓ J).subgroupOf J).subtype)
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at h
  have hp3A : 3 ^ 3 ≤ Nat.card ↥A := by
    rw [hBXcard]
    exact hE
  have hAself : GGTorusSelfCent 3 A := by
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
    have hnp' : (n : G) ^ 3 = 1 := by
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
      rw [MonoidHom.ker_eq_bot (θ : (↥J ⧸ Subgroup.center ↥J) →* R) (MulEquiv.injective θ)]
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
  have hcardA := (hrank ↥J ψ hsurj hker hJperf A hAabel hAI hp3A hAself).2
  have h48 : Nat.card ↥(ggAutomizer J Bs) = 48 := by
    rw [hcardAutEq, hcardA]
  exact h48.ge

theorem ggR4J_card_ge_tw (hKG : GGTwTorusAutKnown) {G : Type} [Group G] [Finite G]
    {Bs J : Subgroup G} {f : ℕ}
    (hBsEA : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hJperf : commutator ↥J = ⊤) (hZ : ∀ g ∈ Subgroup.center ↥J, Nat.Coprime 3 (orderOf g))
    (hInn : ∀ b ∈ Bs, ∃ k ∈ J, ∀ l ∈ J, b * l * b⁻¹ = k * l * k⁻¹)
    (hE : 3 ^ 3 ≤ Nat.card (Bs ⊓ J : Subgroup G))
    (hlab : (3 ∣ 2 ^ f - 1 ∧ GGHasLabel ⟨.twA, 5, f⟩ (↥J ⧸ Subgroup.center ↥J)) ∨
      (3 ∣ 2 ^ f + 1 ∧ GGHasLabel ⟨.A, 5, f⟩ (↥J ⧸ Subgroup.center ↥J)) ∨
      GGHasLabel ⟨.twD, 4, f⟩ (↥J ⧸ Subgroup.center ↥J)) :
    48 ≤ Nat.card (ggAutomizer J Bs) := by
  rcases hlab with ⟨h3, hA⟩ | ⟨h3, hA⟩ | hA
  · have hf : 1 ≤ f := ncd_one_le_of_hasLabel_twA hA
    have hC' : LargeEvenRawDatum ⟨.twA, 5, f⟩
        (fun R _ I F => Nonempty (↥J ⧸ Subgroup.center ↥J ≃* R) ∧ LargeEvenInnSet R ⊆ I) :=
      largeEvenRawDatum_inn_all hA
    have hraw := (hKG f hf).1 h3 _ hC'
    obtain ⟨R, instR, I, F, ⟨⟨⟨θ⟩, hInnI⟩, hrank⟩⟩ := largeEvenRawDatum_exists hraw
    exact ncd_core θ hInnI hrank hBsEA hSC hJperf hZ hInn hE
  · have hf : 1 ≤ f := ncd_one_le_of_hasLabel_A hA
    have hC' : LargeEvenRawDatum ⟨.A, 5, f⟩
        (fun R _ I F => Nonempty (↥J ⧸ Subgroup.center ↥J ≃* R) ∧ LargeEvenInnSet R ⊆ I) :=
      largeEvenRawDatum_inn_all hA
    have hraw := (hKG f hf).2.1 h3 _ hC'
    obtain ⟨R, instR, I, F, ⟨⟨⟨θ⟩, hInnI⟩, hrank⟩⟩ := largeEvenRawDatum_exists hraw
    exact ncd_core θ hInnI hrank hBsEA hSC hJperf hZ hInn hE
  · have hf : 1 ≤ f := ncd_one_le_of_hasLabel_twD hA
    have hC' : LargeEvenRawDatum ⟨.twD, 4, f⟩
        (fun R _ I F => Nonempty (↥J ⧸ Subgroup.center ↥J ≃* R) ∧ LargeEvenInnSet R ⊆ I) :=
      largeEvenRawDatum_inn_all hA
    have hraw := (hKG f hf).2.2 _ hC'
    obtain ⟨R, instR, I, F, ⟨⟨⟨θ⟩, hInnI⟩, hrank⟩⟩ := largeEvenRawDatum_exists hraw
    exact ncd_core θ hInnI hrank hBsEA hSC hJperf hZ hInn hE

end CFSG.StandardType

end
