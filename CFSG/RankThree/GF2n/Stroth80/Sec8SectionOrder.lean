module

public import CFSG.RankThree.GF2n.Stroth80.Sec51Sp
public import CFSG.RankThree.GF2n.Stroth80.Sec83Elem

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open CFSG.ClassicalGroups.F2Fixed CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

theorem sec86_split_of_involution {X M : Type*} [Group X] [AddCommGroup M] [Finite M]
    [DistribMulAction X M] (h2 : ∀ a : M, a + a = 0) {F₁ F₂ : AddSubgroup M}
    (hF : F₁ ⊓ F₂ = ⊥) {l h : X} (hl : ∀ a : M, l • l • a = a)
    (hlF : ∀ a : M, l • a = a → a ∈ F₁) (hh : ∀ b ∈ F₁, h • b ∈ F₂)
    {U : AddSubgroup M} (hlU : ∀ a ∈ U, l • a ∈ U) (hhU : ∀ a ∈ U, h • a ∈ U) :
    (U ⊓ F₁) ⊔ (U ⊓ F₂) = U := by
  have key : ∀ y : M, l • (l • y - y) - (l • y - y) = 0 := by
    intro y
    have e1 : y - l • y - (l • y - y) = (y + y) - (l • y + l • y) := by abel
    rw [smul_sub, hl y, e1, h2 y, h2 (l • y), sub_self]
  obtain ⟨δ, hδ⟩ : ∃ δ : U →+ U, ∀ a : U, ((δ a : U) : M) = l • (a : M) - (a : M) :=
    ⟨AddMonoidHom.mk'
      (fun a : U => (⟨l • (a : M) - (a : M), sub_mem (hlU _ a.2) a.2⟩ : U))
      (fun a b => Subtype.ext (by
        show l • ((a : M) + (b : M)) - ((a : M) + (b : M)) =
          (l • (a : M) - (a : M)) + (l • (b : M) - (b : M))
        rw [smul_add]
        abel)),
     fun a => rfl⟩
  have hfix : ∀ x : δ.ker, l • (x.1 : M) = (x.1 : M) := by
    intro x
    have h0 : ((δ x.1 : U) : M) = 0 := congrArg Subtype.val (AddMonoidHom.mem_ker.mp x.2)
    rw [hδ x.1] at h0
    exact sub_eq_zero.mp h0
  have hkerF : ∀ x : δ.ker, (x.1 : M) ∈ U ⊓ F₁ := fun x =>
    AddSubgroup.mem_inf.mpr ⟨x.1.2, hlF _ (hfix x)⟩
  have hrk : δ.range ≤ δ.ker := by
    intro y hy
    obtain ⟨x, rfl⟩ := AddMonoidHom.mem_range.mp hy
    rw [AddMonoidHom.mem_ker]
    apply Subtype.ext
    rw [hδ (δ x), hδ x]
    exact key x.1
  have hcardU : Nat.card U = Nat.card δ.ker * Nat.card δ.range := by
    have e := AddSubgroup.card_mul_index (H := δ.ker)
    rw [AddSubgroup.index_ker] at e
    exact e.symm
  have hkerle : Nat.card δ.ker ≤ Nat.card ↥(U ⊓ F₁) := by
    refine Nat.card_le_card_of_injective
      (fun x : δ.ker => (⟨x.1.1, hkerF x⟩ : ↥(U ⊓ F₁))) ?_
    rintro ⟨x, hx⟩ ⟨x', hx'⟩ hxx
    exact Subtype.ext (Subtype.ext (congrArg (fun p : ↥(U ⊓ F₁) => p.1) hxx))
  have hrange_le : Nat.card δ.range ≤ Nat.card δ.ker := by
    refine Nat.card_le_card_of_injective
      (fun y : δ.range => (⟨y.1, hrk y.2⟩ : δ.ker)) ?_
    rintro ⟨y, hy⟩ ⟨y', hy'⟩ hyy
    exact Subtype.ext (congrArg (fun p : δ.ker => p.1) hyy)
  have hdiv : Nat.card U ≤ Nat.card ↥(U ⊓ F₁) * Nat.card ↥(U ⊓ F₁) := by
    rw [hcardU]
    exact Nat.mul_le_mul hkerle (hrange_le.trans hkerle)
  have hmemB : ∀ a : M, a ∈ U ⊓ F₁ → h • a ∈ U ⊓ F₂ := fun a ha =>
    AddSubgroup.mem_inf.mpr ⟨hhU a (AddSubgroup.mem_inf.mp ha).1,
      hh a (AddSubgroup.mem_inf.mp ha).2⟩
  have hBA : Nat.card ↥(U ⊓ F₁) ≤ Nat.card ↥(U ⊓ F₂) := by
    refine Nat.card_le_card_of_injective
      (fun a : ↥(U ⊓ F₁) => (⟨h • (a.1 : M), hmemB a.1 a.2⟩ : ↥(U ⊓ F₂))) ?_
    rintro ⟨a, ha⟩ ⟨a', ha'⟩ haa
    have e : h • a = h • a' := congrArg Subtype.val haa
    apply Subtype.ext
    show a = a'
    calc a = h⁻¹ • h • a := (inv_smul_smul h a).symm
      _ = h⁻¹ • h • a' := by rw [e]
      _ = a' := inv_smul_smul h a'
  have hprod : Nat.card ↥(U ⊓ F₁) * Nat.card ↥(U ⊓ F₂) ≤
      Nat.card ↥((U ⊓ F₁) ⊔ (U ⊓ F₂)) := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective
      (fun p : ↥(U ⊓ F₁) × ↥(U ⊓ F₂) =>
        (⟨p.1.1 + p.2.1, AddSubgroup.mem_sup.mpr ⟨p.1.1, p.1.2, p.2.1, p.2.2, rfl⟩⟩ :
          ↥((U ⊓ F₁) ⊔ (U ⊓ F₂)))) ?_
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ hab
    have e : a + b = a' + b' := congrArg Subtype.val hab
    have hd : a - a' = b' - b := by
      have h0 : a - a' - (b' - b) = (a + b) - (a' + b') := by abel
      rw [e, sub_self] at h0
      exact sub_eq_zero.mp h0
    have hz : a - a' ∈ F₁ ⊓ F₂ := by
      refine AddSubgroup.mem_inf.mpr ⟨sub_mem (AddSubgroup.mem_inf.mp ha).2
        (AddSubgroup.mem_inf.mp ha').2, ?_⟩
      rw [hd]
      exact sub_mem (AddSubgroup.mem_inf.mp hb').2 (AddSubgroup.mem_inf.mp hb).2
    rw [hF] at hz
    have haa : a = a' := sub_eq_zero.mp (AddSubgroup.mem_bot.mp hz)
    subst haa
    have hbb : b = b' := add_left_cancel e
    subst hbb
    rfl
  have hTU : (U ⊓ F₁) ⊔ (U ⊓ F₂) ≤ U := sup_le inf_le_left inf_le_left
  have hcard : Nat.card U ≤ Nat.card ↥((U ⊓ F₁) ⊔ (U ⊓ F₂)) :=
    hdiv.trans ((Nat.mul_le_mul le_rfl hBA).trans hprod)
  exact AddSubgroup.eq_of_le_of_card_ge hTU hcard

theorem exists_nonA2_mem_LspGL' {m : ℕ} {K : Type} [Field K] {u : Fin m ⊕ Fin m → K}
    (hu : u ≠ 0) : ∃ g ∈ LspGL m K u, ∃ y : Fin m ⊕ Fin m → K,
      spForm m K y ((g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ y) ≠ 0 := by
  obtain ⟨y₀, hy₀⟩ : ∃ y : Fin m ⊕ Fin m → K, spForm m K y u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu ((spForm_nondegenerate (m := m) (K := K)).2 u hcon)
  obtain ⟨A, hA, hAx⟩ := exists_transvection_LspGL u
  refine ⟨A, hA, y₀, ?_⟩
  rw [hAx, map_add, map_smul, spForm_self, zero_add, smul_eq_mul]
  exact mul_ne_zero hy₀ hy₀

theorem sec8_invariant_section {R N P I L₁ L₂ A₁ A₂ U : Subgroup G} {m : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K 2] (φ : ↥R →* GL (Fin m ⊕ Fin m) K) (hφ : φ.range = StatedSp m K)
    (hm : 1 ≤ m) (hNφ : φ.ker = N.subgroupOf R) (hP : ∀ ρ ∈ R, ∀ x ∈ P, ρ * x * ρ⁻¹ ∈ P)
    (hI : ∀ ρ ∈ R, ∀ x ∈ I, ρ * x * ρ⁻¹ ∈ I) (hN : ∀ n ∈ N, ∀ y ∈ P, ⁅n, y⁆ ∈ I)
    (hd : IsOppDecomp P I L₁ L₂ A₁ A₂) (h₁ : L₁ ≤ R) (h₂ : L₂ ≤ R)
    {u u' : Fin m ⊕ Fin m → K} (huu' : spForm m K u u' ≠ 0) (hu : u ≠ 0)
    (hL₁ : (L₁.subgroupOf R).map φ = LspGL m K u) (hL₂ : (L₂.subgroupOf R).map φ = LspGL m K u')
    (hsq : ∀ x ∈ L₁, x ^ 2 ∈ N) {r : G} (hr : r ∈ R) (hrL : conjSubgroup r L₁ = L₂)
    (hIU : I ≤ U) (hUP : U ≤ P) (hUinv : ∀ ρ ∈ R, conjSubgroup ρ U = U) :
    IsOppDecomp U I L₁ L₂ (U ⊓ A₁) (U ⊓ A₂) ∧
      ∃ a : ℕ, Nat.card ↥U = Nat.card ↥I * Nat.card K ^ (2 ^ m * a) := by
  classical
  have hsec : SecHyp R P I := SecHyp.of_isOppDecomp hd hP hI
  obtain ⟨Mo, iMo, iAct, κ, hκ, hkerAct⟩ := exists_sectionModule_ker hNφ hsec hN
  haveI : Finite Mo := hκ.finite
  obtain ⟨e₁, e₂⟩ := fixedSub_eq_secSub_of_isOppDecomp hP hκ hd h₁ h₂
  have hdec := isCompl_fixedSub_of_isOppDecomp hP hκ hd h₁ h₂
  obtain ⟨g₀, hg₀, y₀, hy₀⟩ := exists_nonA2_mem_LspGL' hu
  have hg₀' : g₀ ∈ (L₁.subgroupOf R).map φ := by rw [hL₁]; exact hg₀
  obtain ⟨l, hl, hlg⟩ := Subgroup.mem_map.mp hg₀'
  have hF3 := stroth_2_1_fixed_of_hom φ hφ hm hκ.two hkerAct huu' hL₁ hL₂ hdec (x := l)
    (by rw [hlg]; exact hg₀) ⟨y₀, by rw [hlg]; exact hy₀⟩
  set F₁ := fixedSub Mo ((L₁.subgroupOf R : Subgroup ↥R) : Set ↥R) with hF₁
  set F₂ := fixedSub Mo ((L₂.subgroupOf R : Subgroup ↥R) : Set ↥R) with hF₂
  have hlF : ∀ a : Mo, l • a = a → a ∈ F₁ := by
    intro a ha
    have hle : F₁ ≤ fixedSub Mo {l} := fixedSub_anti (Set.singleton_subset_iff.mpr hl)
    have hcard := card_eq_card_fixedSub_mul_card_range (M := Mo) l
    rw [hF3.1, hF3.2, sq] at hcard
    have hpos : 0 < Nat.card F₁ := Nat.card_pos
    have h1 : Nat.card (fixedSub Mo {l}) = Nat.card F₁ := by
      have := Nat.eq_of_mul_eq_mul_right hpos hcard
      exact this.symm
    have hEq : F₁ = fixedSub Mo {l} := AddSubgroup.eq_of_le_of_card_ge hle h1.le
    rw [hEq]
    exact fun g hg => by rw [Set.mem_singleton_iff.mp hg]; exact ha
  have hl2 : ∀ a : Mo, l • l • a = a := by
    intro a
    have hlL : (l : G) ∈ L₁ := Subgroup.mem_subgroupOf.mp hl
    have hmem : l * l ∈ φ.ker := by
      rw [hNφ, Subgroup.mem_subgroupOf]
      have := hsq (l : G) hlL
      simpa [sq] using this
    rw [← mul_smul]
    exact hkerAct _ hmem a
  set h : ↥R := ⟨r, hr⟩ with hhdef
  have hh : ∀ b ∈ F₁, h • b ∈ F₂ := by
    intro b hb g hg
    have hgL : (g : G) ∈ L₂ := Subgroup.mem_subgroupOf.mp hg
    have hyL : (r : G)⁻¹ * (g : G) * r ∈ L₁ := by
      rw [← hrL] at hgL
      exact mem_conjSubgroup.mp hgL
    have hy : (⟨r⁻¹ * (g : G) * r, R.mul_mem (R.mul_mem (R.inv_mem hr) g.2) hr⟩ : ↥R) ∈
        L₁.subgroupOf R := Subgroup.mem_subgroupOf.mpr hyL
    have hyb := hb _ hy
    have e : g * h =
        h * (⟨r⁻¹ * (g : G) * r, R.mul_mem (R.mul_mem (R.inv_mem hr) g.2) hr⟩ : ↥R) := by
      apply Subtype.ext
      simp [hhdef]
      group
    rw [← mul_smul, e, mul_smul, hyb]
  have hUsec := fun ρ : ↥R => (conjSubgroup_eq_self_iff_secSub hsec hκ ρ hIU hUP).mp
    (hUinv ρ ρ.2)
  have hlU : ∀ a ∈ secSub κ U, l • a ∈ secSub κ U := by
    intro a ha
    have h1 : l • a ∈ (secSub κ U).map (DistribSMul.toAddMonoidHom Mo l) :=
      AddSubgroup.mem_map.mpr ⟨a, ha, rfl⟩
    rwa [hUsec l] at h1
  have hhU : ∀ a ∈ secSub κ U, h • a ∈ secSub κ U := by
    intro a ha
    have h1 : h • a ∈ (secSub κ U).map (DistribSMul.toAddMonoidHom Mo h) :=
      AddSubgroup.mem_map.mpr ⟨a, ha, rfl⟩
    rwa [hUsec h] at h1
  have hsplit := sec86_split_of_involution hκ.two hdec.inf_eq_bot hl2 hlF hh hlU hhU
  obtain ⟨hIA₁, hA₁P, hIA₂, hA₂P, hsup, hinf, hcomm, hsq', hA₁iff, hA₂iff⟩ := hd
  have hIUA₁ : I ≤ U ⊓ A₁ := le_inf hIU hIA₁
  have hIUA₂ : I ≤ U ⊓ A₂ := le_inf hIU hIA₂
  have hUA₁P : U ⊓ A₁ ≤ P := inf_le_left.trans hUP
  have hUA₂P : U ⊓ A₂ ≤ P := inf_le_left.trans hUP
  have hsupU : (U ⊓ A₁) ⊔ (U ⊓ A₂) = U := by
    have h1 : secSub κ ((U ⊓ A₁) ⊔ (U ⊓ A₂)) = secSub κ U := by
      rw [secSub_sup hUA₁P hUA₂P, secSub_inf hκ hIU, secSub_inf hκ hIU, ← e₁, ← e₂]
      exact hsplit
    exact (secSub_inj hκ (hIUA₁.trans le_sup_left) (sup_le hUA₁P hUA₂P) hIU hUP).mp h1
  have hd' : IsOppDecomp U I L₁ L₂ (U ⊓ A₁) (U ⊓ A₂) := by
    refine ⟨hIUA₁, inf_le_left, hIUA₂, inf_le_left, hsupU, ?_, fun x hx y hy => hcomm x (hUP hx) y
      (hUP hy), fun x hx => hsq' x (hUP hx), fun x hx => ?_, fun x hx => ?_⟩
    · refine le_antisymm ?_ (le_inf hIUA₁ hIUA₂)
      calc (U ⊓ A₁) ⊓ (U ⊓ A₂) ≤ A₁ ⊓ A₂ := inf_le_inf inf_le_right inf_le_right
        _ = I := hinf
    · exact ⟨fun h => (hA₁iff x (hUP hx)).mp h.2, fun h => ⟨hx, (hA₁iff x (hUP hx)).mpr h⟩⟩
    · exact ⟨fun h => (hA₂iff x (hUP hx)).mp h.2, fun h => ⟨hx, (hA₂iff x (hUP hx)).mpr h⟩⟩
  refine ⟨hd', ?_⟩
  exact stroth_2_1_ii_secSp hm φ hφ hNφ
    (fun ρ hρ x hx => conj_mem_of_conjSubgroup_eq (hUinv ρ hρ) hx)
    hI (fun n hn y hy => hN n hn y (hUP hy)) hd' h₁ h₂ huu' hL₁ hL₂

section Count


theorem sec8_section_commSec_card {R N P I L₁ L₂ A₁ A₂ : Subgroup G} {m : ℕ} {K : Type}
    [Field K] [Finite K] [CharP K 2] (φ : ↥R →* GL (Fin m ⊕ Fin m) K)
    (hφ : φ.range = StatedSp m K) (hm : 1 ≤ m) (hNφ : φ.ker = N.subgroupOf R)
    (hP : ∀ ρ ∈ R, ∀ x ∈ P, ρ * x * ρ⁻¹ ∈ P) (hI : ∀ ρ ∈ R, ∀ x ∈ I, ρ * x * ρ⁻¹ ∈ I)
    (hN : ∀ n ∈ N, ∀ y ∈ P, ⁅n, y⁆ ∈ I) (hd : IsOppDecomp P I L₁ L₂ A₁ A₂) (h₁ : L₁ ≤ R)
    (h₂ : L₂ ≤ R) {u u' : Fin m ⊕ Fin m → K} (huu' : spForm m K u u' ≠ 0)
    (hL₁ : (L₁.subgroupOf R).map φ = LspGL m K u) (hL₂ : (L₂.subgroupOf R).map φ = LspGL m K u')
    {x : G} (hxL : x ∈ L₁) (hx1 : φ ⟨x, h₁ hxL⟩ ≠ 1) :
    (SpNonA2 (φ ⟨x, h₁ hxL⟩) → Nat.card ↥(CommSec P I x) ^ 2 = Nat.card ↥I * Nat.card ↥P) ∧
      (¬ SpNonA2 (φ ⟨x, h₁ hxL⟩) →
        Nat.card ↥I ^ 3 * Nat.card ↥P ≤ Nat.card ↥(CommSec P I x) ^ 4) := by
  classical
  have hsec : SecHyp R P I := SecHyp.of_isOppDecomp hd hP hI
  obtain ⟨Mo, iMo, iAct, κ, hκ, hker⟩ := exists_sectionModule_ker hNφ hsec hN
  haveI : Finite Mo := hκ.finite
  have hdec := isCompl_fixedSub_of_isOppDecomp hP hκ hd h₁ h₂
  have hzL' : φ ⟨x, h₁ hxL⟩ ∈ LspGL m K u := by
    rw [← hL₁]
    exact ⟨⟨x, h₁ hxL⟩, Subgroup.mem_subgroupOf.mpr hxL, rfl⟩
  have hIP : I ≤ P := hd.1.trans hd.2.1
  have hcc : Nat.card ↥(CommSec P I x) =
      Nat.card ↥I * Nat.card ↥(comm Mo (⟨x, h₁ hxL⟩ : ↥R)).range :=
    natCard_commutator_sup hκ hP hIP ⟨x, h₁ hxL⟩
  have hPc : Nat.card ↥P = Nat.card ↥I * Nat.card Mo := natCard_eq_of_isSecMod hIP hκ
  refine ⟨fun hna => ?_, fun hna => ?_⟩
  · obtain ⟨hrange, hcard⟩ := stroth_2_1_fixed_of_hom φ hφ hm hκ.two hker huu' hL₁ hL₂ hdec hzL'
      hna
    rw [hcc, hPc, hrange, hcard]
    ring
  · have hle := stroth_2_1_a2_of_fixed fixedNonA2Fact φ hφ hm hκ.two hker huu' hL₁ hL₂ hdec hzL'
      hx1 hna
    rw [hcc, hPc]
    calc Nat.card ↥I ^ 3 * (Nat.card ↥I * Nat.card Mo)
        ≤ Nat.card ↥I ^ 3 * (Nat.card ↥I *
          Nat.card ↥(comm Mo (⟨x, h₁ hxL⟩ : ↥R)).range ^ 4) := by gcongr
      _ = (Nat.card ↥I * Nat.card ↥(comm Mo (⟨x, h₁ hxL⟩ : ↥R)).range) ^ 4 := by ring

end Count

end CFSG.RankThree.GF2n.Stroth80
