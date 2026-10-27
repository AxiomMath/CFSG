module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoKey
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSpNsComp

public section

open Polynomial Module CFSG.RankThree.Classical CFSG.Assembly CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open scoped commutatorElement

namespace CFSG.StandardType

namespace A6InsideSp

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType.ChoiceTwo

section FixedInf

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem spFixedFactor_inf_spSupported_phi3 (hK : Nat.card K = 2) {w : StatedSp n K}
    (hw : w ^ 3 = 1) : spFixedFactor w ⊓ spSupported w {phi3 K} = ⊥ := by
  refine le_antisymm ?_ bot_le
  rintro g ⟨hg₁, hg₂⟩
  rw [Subgroup.mem_bot]
  refine eq_of_spEnd_eq' fun v => ?_
  set T : Module.End K (Fin n ⊕ Fin n → K) := spEnd w with hT
  have hT3 : ∀ x, T (T (T x)) = x := fun x => by
    rw [hT, ← spEnd_mul_apply, ← spEnd_mul_apply, ← pow_three', hw, spEnd_one_apply]
  have hc2 : ∀ x : Fin n ⊕ Fin n → K, x + x = 0 := add_self_eq_zero_of_charTwo (K := K)
  obtain ⟨a, ha⟩ : ∃ a, a = T v := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = T a := ⟨_, rfl⟩
  have hTb : T b = v := by rw [hb, ha, hT3]
  obtain ⟨w₁, hw₁⟩ : ∃ w, w = b + a + v := ⟨_, rfl⟩
  obtain ⟨w₂, hw₂⟩ : ∃ w, w = b + a := ⟨_, rfl⟩
  have hTw₁ : T w₁ = w₁ := by
    rw [hw₁, map_add, map_add, hTb, ← hb, ← ha]
    abel
  have hTw₂ : T w₂ = v + b := by rw [hw₂, map_add, hTb, ← hb]
  have hPw₂ : T (T w₂) + T w₂ + w₂ = 0 := by
    rw [hTw₂, map_add, hTb, ← ha, hw₂]
    calc a + v + (v + b) + (b + a) = (a + a) + ((v + v) + (b + b)) := by abel
      _ = 0 := by rw [hc2, hc2, hc2, add_zero, add_zero]
  have hv : v = w₁ + w₂ := by
    rw [hw₁, hw₂]
    calc v = v + ((b + a) + (b + a)) := by rw [hc2, add_zero]
      _ = b + a + v + (b + a) := by abel
  have hgw₂ : spEnd g w₂ = w₂ :=
    fix_of_mem_spSupported hg₁ (phi3_irreducible hK) monic_phi3
      (fun h => phi3_ne_X_sub_one h) (by rw [aeval_phi3_apply]; exact hPw₂)
  have hgw₁ : spEnd g w₁ = w₁ :=
    fix_of_mem_spSupported hg₂ irreducible_X_sub_one monic_X_sub_one
      (fun h => phi3_ne_X_sub_one h.symm) (by rw [aeval_X_sub_one_apply, sub_eq_zero]; exact hTw₁)
  rw [hv, map_add, hgw₁, hgw₂, spEnd_one_apply]

theorem commute_of_commute_mul (hK : Nat.card K = 2) {w g m₁ m₂ : StatedSp n K}
    (hw : w ^ 3 = 1) (hm₁ : m₁ ∈ spFixedFactor w) (hm₂ : m₂ ∈ spSupported w {phi3 K})
    (hg : g ∈ Subgroup.centralizer {w}) (hgm : g * (m₁ * m₂) = m₁ * m₂ * g) :
    g * m₁ = m₁ * g := by
  set a := g * m₁ * g⁻¹ with ha
  set b := g * m₂ * g⁻¹ with hb
  have haA : a ∈ spFixedFactor w := spFixedFactor_normalized w g hg m₁ hm₁
  have hbB : b ∈ spSupported w {phi3 K} :=
    SevSpNs.spSupported_normalized w {phi3 K} g hg m₂ hm₂
  have hab : a * b = m₁ * m₂ := by
    calc a * b = g * (m₁ * m₂) * g⁻¹ := by rw [ha, hb]; group
      _ = m₁ * m₂ * g * g⁻¹ := by rw [hgm]
      _ = m₁ * m₂ := by group
  have haeq : a⁻¹ * m₁ = b * m₂⁻¹ := by
    calc a⁻¹ * m₁ = a⁻¹ * (m₁ * m₂) * m₂⁻¹ := by group
      _ = a⁻¹ * (a * b) * m₂⁻¹ := by rw [hab]
      _ = b * m₂⁻¹ := by group
  have hone : a⁻¹ * m₁ = 1 := by
    have hmem : a⁻¹ * m₁ ∈ spFixedFactor w ⊓ spSupported w {phi3 K} := by
      refine ⟨Subgroup.mul_mem (spFixedFactor w) (Subgroup.inv_mem _ haA) hm₁, ?_⟩
      rw [haeq]
      exact Subgroup.mul_mem (spSupported w {phi3 K}) hbB (Subgroup.inv_mem _ hm₂)
    rw [spFixedFactor_inf_spSupported_phi3 hK hw] at hmem
    exact Subgroup.mem_bot.mp hmem
  have ha1 : a = m₁ := inv_mul_eq_one.mp hone
  rw [ha] at ha1
  exact mul_inv_eq_iff_eq_mul.mp ha1

end FixedInf

section Frame

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {L : Type} [Field L]
  [Algebra K L] {ζ : L} {E : Subgroup (StatedSp n K)} (F : SpFrame K n ζ E)

theorem exists_mul_eq_of_mem_centralizer (hK : Nat.card K = 2) (hζo : IsPrimitiveRoot ζ 3)
    (f : Fin F.s → ZMod 3) {g : StatedSp n K} (hg : g ∈ Subgroup.centralizer {F.tor f}) :
    ∃ g₁ ∈ spFixedFactor (F.tor f), ∃ g₂ ∈ spSupported (F.tor f) {phi3 K}, g = g₁ * g₂ := by
  by_cases hf : f = 0
  · subst hf
    refine ⟨g, ?_, 1, ?_, by rw [mul_one]⟩
    · rw [F.tor_zero]
      change g ∈ spSupported (1 : StatedSp n K) {X - 1}
      refine mem_spSupported_of hK (by simp) (by group)
        (fun h => absurd (Set.mem_singleton _) h) fun _ v hv => ?_
      rw [spEnd_one_apply, spEnd_one_apply] at hv
      have hv0 : v = 0 := by
        rw [add_self_eq_zero_of_charTwo (K := K), zero_add] at hv
        exact hv
      rw [hv0, map_zero]
    · rw [F.tor_zero]
      exact one_mem _
  · haveI : NeZero n := ⟨by
      intro h0
      subst h0
      have hsub : Subsingleton (Fin F.s → L) :=
        ⟨fun a b => F.Φ.injective (Subsingleton.elim (F.Φ a) (F.Φ b))⟩
      haveI := hsub
      have hs : F.s = 0 := by
        by_contra hs
        obtain ⟨i⟩ := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hs)
        have h1 : (Pi.single i (1 : L) : Fin F.s → L) = 0 := Subsingleton.elim _ _
        have h2 := congrFun h1 i
        rw [Pi.single_eq_same, Pi.zero_apply] at h2
        exact one_ne_zero h2
      haveI : IsEmpty (Fin F.s) := by rw [hs]; infer_instance
      exact hf (Subsingleton.elim f 0)⟩
    have hw : F.tor f ^ 3 = 1 := F.tor_pow_three hζo.pow_eq_one f
    have blocks := F.blocks_tor hK hζo hf
    have hT3 : spEnd (F.tor f) ^ 3 = 1 := by
      rw [← ChoiceTwo.spEnd_pow, hw, spEnd_one]
    set A := spFixedFactor (F.tor f)
    set B := spSupported (F.tor f) {phi3 K}
    have hA : A ≤ Subgroup.centralizer {F.tor f} := spFixedFactor_le_centralizer (F.tor f)
    have hB : B ≤ Subgroup.centralizer {F.tor f} :=
      SevSpNs.spSupported_le_centralizer (F.tor f) {phi3 K}
    have hfac : ∀ O : reciprocalOrbits (spEnd (F.tor f)),
        spSupported (F.tor f) (O : Set K[X]) ≤ A ⊔ B := by
      rintro ⟨O, k, hk, rfl⟩
      rcases primaryFactor_cases hK hT3 hk with rfl | rfl
      · refine le_sup_of_le_left (le_of_eq ?_)
        change spSupported (F.tor f) {X - 1, reciprocalPolynomial (X - 1)} =
          spSupported (F.tor f) {X - 1}
        rw [KCSpIsotypic.reciprocalPolynomial_X_sub_one, Set.pair_eq_singleton]
      · change spSupported (F.tor f) {phi3 K, reciprocalPolynomial (phi3 K)} ≤ A ⊔ B
        rw [reciprocal_phi3, Set.pair_eq_singleton]
        exact le_sup_right
    have hCw : Subgroup.centralizer {F.tor f} ≤ A ⊔ B := by
      rw [← blocks.directProduct.2.2]
      exact iSup_le hfac
    have hsup : A ⊔ B = Subgroup.centralizer {F.tor f} := le_antisymm (sup_le hA hB) hCw
    haveI hAn : (A.subgroupOf (Subgroup.centralizer {F.tor f})).Normal :=
      SevSpNs.normal_subgroupOf_of_normalized hA (spFixedFactor_normalized (F.tor f))
    have hsub : A.subgroupOf (Subgroup.centralizer {F.tor f}) ⊔
        B.subgroupOf (Subgroup.centralizer {F.tor f}) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hA hB, hsup, Subgroup.subgroupOf_self]
    have hg' : (⟨g, hg⟩ : Subgroup.centralizer {F.tor f}) ∈
        A.subgroupOf (Subgroup.centralizer {F.tor f}) ⊔
          B.subgroupOf (Subgroup.centralizer {F.tor f}) := by
      rw [hsub]
      exact Subgroup.mem_top _
    obtain ⟨⟨a, haC⟩, haA, ⟨b, hbC⟩, hbB, hab⟩ :=
      (Subgroup.mem_sup_of_normal_left).mp hg'
    exact ⟨a, haA, b, hbB, (congrArg Subtype.val hab).symm⟩

section Component

variable [NeZero n]

theorem le_spFixedFactor_or_le_spSupported (hK : Nat.card K = 2) (hζo : IsPrimitiveRoot ζ 3)
    {f : Fin F.s → ZMod 3} {D Q : Subgroup (StatedSp n K)}
    (hDw : D ≤ Subgroup.centralizer {F.tor f})
    (hCw : Subgroup.centralizer (D : Set (StatedSp n K)) ≤ Subgroup.centralizer {F.tor f})
    (hQ : IsComponentOf Q (Subgroup.centralizer (D : Set (StatedSp n K)))) :
    Q ≤ spFixedFactor (F.tor f) ∨ Q ≤ spSupported (F.tor f) {phi3 K} := by
  classical
  have hw : F.tor f ^ 3 = 1 := F.tor_pow_three hζo.pow_eq_one f
  set A := spFixedFactor (F.tor f)
  set B := spSupported (F.tor f) {phi3 K}
  set C : Subgroup (StatedSp n K) := Subgroup.centralizer (D : Set (StatedSp n K)) with hCdef
  set A₁ : Subgroup (StatedSp n K) := A ⊓ C
  set A₂ : Subgroup (StatedSp n K) := B ⊓ C
  have hfac : ∀ g ∈ C, ∃ g₁ ∈ A₁, ∃ g₂ ∈ A₂, g = g₁ * g₂ := by
    intro g hg
    have hgCw : g ∈ Subgroup.centralizer {F.tor f} := hCw hg
    obtain ⟨p₁, hp₁, p₂, hp₂, hgp⟩ :=
      exists_mul_eq_of_mem_centralizer (F := F) hK hζo f hgCw
    have hp₁C : p₁ ∈ C := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      obtain ⟨m₁, hm₁, m₂, hm₂, hdm⟩ :=
        exists_mul_eq_of_mem_centralizer (F := F) hK hζo f (hDw hd)
      have hgd : Commute g d := (Subgroup.mem_centralizer_iff.mp hg d hd).symm
      have hgm : g * (m₁ * m₂) = m₁ * m₂ * g := by
        rw [← hdm]
        exact hgd.eq
      have hgm₁ : g * m₁ = m₁ * g :=
        commute_of_commute_mul hK hw hm₁ hm₂ hgCw hgm
      have hp₂m₁ : Commute p₂ m₁ :=
        (commute_of_mem_spFixedFactor hK hw (O := {phi3 K})
          (fun h => phi3_ne_X_sub_one h.symm) hm₁ hp₂).symm
      have hp₁m₁ : Commute p₁ m₁ := by
        have hp₁eq : p₁ = g * p₂⁻¹ := by rw [hgp]; group
        rw [hp₁eq]
        have hc : Commute g m₁ := hgm₁
        exact hc.mul_left hp₂m₁.inv_left
      have hp₁m₂ : Commute p₁ m₂ :=
        commute_of_mem_spFixedFactor hK hw (O := {phi3 K})
          (fun h => phi3_ne_X_sub_one h.symm) hp₁ hm₂
      have hp₁d : Commute p₁ (m₁ * m₂) := hp₁m₁.mul_right hp₁m₂
      rw [hdm]
      exact hp₁d.eq.symm
    have hp₂C : p₂ ∈ C := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have hp₁d : Commute p₁ d :=
        (Subgroup.mem_centralizer_iff.mp hp₁C d hd).symm
      have hgd : Commute g d := (Subgroup.mem_centralizer_iff.mp hg d hd).symm
      have hp₂eq : p₂ = p₁⁻¹ * g := by rw [hgp]; group
      rw [hp₂eq]
      exact (hp₁d.inv_left.mul_left hgd).symm
    exact ⟨p₁, ⟨hp₁, hp₁C⟩, p₂, ⟨hp₂, hp₂C⟩, hgp⟩
  have hsup : A₁ ⊔ A₂ = C := by
    refine le_antisymm (sup_le inf_le_right inf_le_right) ?_
    intro g hg
    obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hfac g hg
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hg₁) (Subgroup.mem_sup_right hg₂)
  have hnA₁ : (A₁.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro h k hh hk
    refine ⟨spFixedFactor_normalized (F.tor f) k (hCw hk) h hh.1, ?_⟩
    exact Subgroup.mul_mem C (Subgroup.mul_mem C hk hh.2) (Subgroup.inv_mem C hk)
  have hnA₂ : (A₂.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro h k hh hk
    refine ⟨SevSpNs.spSupported_normalized (F.tor f) {phi3 K} k (hCw hk) h hh.1, ?_⟩
    exact Subgroup.mul_mem C (Subgroup.mul_mem C hk hh.2) (Subgroup.inv_mem C hk)
  rcases CoordSL.le_or_commutator_eq_bot_of_normal hQ inf_le_right hnA₁ with h₁ | hc₁
  · exact Or.inl (h₁.trans inf_le_left)
  rcases CoordSL.le_or_commutator_eq_bot_of_normal hQ inf_le_right hnA₂ with h₂ | hc₂
  · exact Or.inr (h₂.trans inf_le_left)
  exfalso
  have hQc₁ : Q ≤ Subgroup.centralizer (A₁ : Set (StatedSp n K)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc₁
  have hQc₂ : Q ≤ Subgroup.centralizer (A₂ : Set (StatedSp n K)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc₂
  have hle : Q ≤ Subgroup.centralizer (C : Set (StatedSp n K)) := by
    have hcl : Subgroup.closure ((A₁ : Set (StatedSp n K)) ∪ (A₂ : Set (StatedSp n K))) =
        A₁ ⊔ A₂ := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    rw [← hsup, ← hcl, Subgroup.centralizer_closure]
    intro q hq
    have h1 : q ∈ Subgroup.centralizer (A₁ : Set (StatedSp n K)) := hQc₁ hq
    have h2 : q ∈ Subgroup.centralizer (A₂ : Set (StatedSp n K)) := hQc₂ hq
    rw [Subgroup.mem_centralizer_iff] at h1 h2 ⊢
    intro y hy
    rcases hy with hy | hy
    · exact h1 y hy
    · exact h2 y hy
  exact CFSG.LocalAnalysis.ComponentInitial.not_le_centralizer_self_of_isQuasisimple
    hQ.2.2 (hle.trans (Subgroup.centralizer_le hQ.1))

end Component

end Frame

section Components

variable {G : Type*} [Group G]

theorem isComponentOf_centralizer_of_inf {x : G} {D L₀ J : Subgroup G}
    (hxD : x ∈ D) (hLx : L₀ ≤ Subgroup.centralizer {x})
    (hLn : ∀ m ∈ Subgroup.centralizer ({x} : Set G), ∀ g ∈ L₀, m * g * m⁻¹ ∈ L₀)
    (hJ : IsComponentOf J (L₀ ⊓ Subgroup.centralizer (D : Set G))) :
    IsComponentOf J (Subgroup.centralizer (D : Set G)) := by
  have hle : L₀ ⊓ Subgroup.centralizer (D : Set G) ≤ Subgroup.centralizer (D : Set G) :=
    inf_le_right
  have hCDx : Subgroup.centralizer (D : Set G) ≤ Subgroup.centralizer {x} :=
    Subgroup.centralizer_le fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      exact hy ▸ hxD
  have hnorm : ((L₀ ⊓ Subgroup.centralizer (D : Set G)).subgroupOf
      (Subgroup.centralizer (D : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro h k hh hk
    exact ⟨hLn k (hCDx hk) h hh.1,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hh.2) (Subgroup.inv_mem _ hk)⟩
  exact ⟨hJ.1.trans hle,
    hJ.2.1.trans (IsSubnormal.step hle hnorm (IsSubnormal.refl _)), hJ.2.2⟩

theorem isComponentOf_of_le_normalized {J A S M : Subgroup G}
    (hJ : IsComponentOf J A) (hJS : J ≤ S) (hSA : S ≤ A) (hSM : S ≤ M)
    (hn : ∀ m ∈ M, ∀ g ∈ S, m * g * m⁻¹ ∈ S) : IsComponentOf J M := by
  have hJS' : J ⊓ S = J := inf_eq_left.mpr hJS
  have hsubS : IsSubnormal J S := by
    have h := hJ.2.1.inf_of_le hSA
    rwa [hJS'] at h
  have hnorm : (S.subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hSM]
    exact fun h k hh hk => hn k hk h hh
  exact ⟨hJS.trans hSM, hsubS.trans (IsSubnormal.step hSM hnorm (IsSubnormal.refl _)),
    hJ.2.2⟩

end Components

end A6InsideSp

end CFSG.StandardType
