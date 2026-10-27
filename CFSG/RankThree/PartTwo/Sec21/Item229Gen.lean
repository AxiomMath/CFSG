module

public import CFSG.RankThree.PartTwo.Sec21.Item22DStar
public import CFSG.RankThree.PartTwo.Sec21.Item22Refl
import CFSG.RankThree.PartTwo.Sec21.Item22L2

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

variable {G : Type} [Group G]

theorem kOf_eq_of_fixedInG_eq {A : Subgroup G} {φ ψ : MulAut A}
    (h : fixedInG A φ = fixedInG A ψ) : kOf A φ = kOf A ψ := by
  have hk : kZero A φ = kZero A ψ := by rw [kZero, kZero, h]
  unfold kOf
  rw [hk]

theorem iGroup_eq_iSup_of_fuse [Finite G] (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A) {T : Set (MulAut A)}
    (hT : T ⊆ dStar A)
    (hfuse : ∀ φ ∈ dStar A, ∃ g ∈ Subgroup.closure T, ∃ τ ∈ T, g * τ * g⁻¹ = φ) :
    iGroup A = ⨆ τ ∈ T, kOf A τ := by
  set I₀ := ⨆ τ ∈ T, kOf A τ with hI₀
  have hcl : Subgroup.closure T ≤ starOf A I₀ := by
    rw [Subgroup.closure_le]
    intro τ hτ
    exact starOf_mono A (le_iSup₂_of_le τ hτ le_rfl) (mem_starOf_kOf h222 hpair hK (hT hτ))
  apply le_antisymm
  · refine iSup₂_le fun φ hφ => ?_
    obtain ⟨g, hg, τ, hτ, rfl⟩ := hfuse φ hφ
    obtain ⟨w, hwI, rfl⟩ := hcl hg
    change kOf A (wConj A w * τ * (wConj A w)⁻¹) ≤ I₀
    rw [kOf_conj_of_unique hK w (hT hτ)]
    rintro _ ⟨x, hx, rfl⟩
    have hwI' : (w : G) ∈ I₀ := Subgroup.mem_subgroupOf.mp hwI
    have hτI : kOf A τ ≤ I₀ := le_iSup₂_of_le (f := fun τ _ => kOf A τ) τ hτ le_rfl
    have hxI : x ∈ I₀ := hτI hx
    exact I₀.mul_mem (I₀.mul_mem hwI' hxI) (I₀.inv_mem hwI')
  · exact iSup₂_le fun τ hτ => kOf_le_iGroup (hT hτ)

theorem inf_centralizer_kOf_eq [Finite G] (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A) {φ : MulAut A}
    (hφ : φ ∈ dStar A) :
    A ⊓ Subgroup.centralizer (kOf A φ : Set G) = fixedInG A φ := by
  apply le_antisymm
  · rintro a ⟨haA, haC⟩
    obtain ⟨j, hjK, -, hj⟩ := exists_involution_kOf_wConj_eq h222 hpair hK hφ
    refine ⟨⟨a, haA⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_fixedSubgroupOf, ← hj]
    apply Subtype.ext
    rw [wConj_apply]
    change (j : G) * a * (j : G)⁻¹ = a
    rw [Subgroup.mem_centralizer_iff.mp haC j hjK, mul_inv_cancel_right]
  · rintro _ ⟨b, hb, rfl⟩
    refine ⟨b.2, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp
      (kZero_le_centralizer A φ (kOf_le_kZero hK hφ hx)) b ⟨b, hb, rfl⟩).symm

theorem fixedSubgroupOf_ne_of_ne [Finite G] (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A) {φ ψ : MulAut A}
    (hφ : φ ∈ dStar A) (hψ : ψ ∈ dStar A) (hne : φ ≠ ψ) :
    fixedSubgroupOf φ ≠ fixedSubgroupOf ψ := by
  intro hfix
  apply hne
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hA3 : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hAe.2 a a.2)
  have hfixG : fixedInG A φ = fixedInG A ψ := by rw [fixedInG, fixedInG, hfix]
  have hKeq := kOf_eq_of_fixedInG_eq hfixG
  obtain ⟨⟨n, ⟨e⟩⟩, z, hcz, hzK, hz3⟩ := exists_commOf_eq_zpowers_mem_kOf h222 hpair hK hφ
  obtain ⟨-, z', hcz', hzK', hz3'⟩ := exists_commOf_eq_zpowers_mem_kOf h222 hpair hK hψ
  rw [← hKeq] at hzK'
  set M : Subgroup A := (kOf A φ).comap A.subtype with hM
  have hcardM : Nat.card M ≤ 3 := by
    let g := (commHom hAc φ).comp M.subtype
    have hginj : Function.Injective g := by
      rw [injective_iff_map_eq_one]
      intro m hm
      have hfa : (m : A) ∈ fixedSubgroupOf φ := by
        rw [← ker_commHom hAc φ]
        exact hm
      have haC : ((m : A) : G) ∈ A ⊓ Subgroup.centralizer (kOf A φ : Set G) := by
        rw [inf_centralizer_kOf_eq h222 hpair hK hφ]
        exact ⟨m, hfa, rfl⟩
      have h1 : (⟨((m : A) : G), m.2⟩ : kOf A φ) = 1 :=
        eq_one_of_forall_commute_of_mulEquiv_projSL e fun x =>
          Subtype.ext (Subgroup.mem_centralizer_iff.mp haC.2 x x.2)
      have h2 : ((m : A) : G) = 1 := congrArg Subtype.val h1
      exact Subtype.ext (Subtype.ext h2)
    have hle : g.range ≤ commOf φ := by
      rintro _ ⟨y, rfl⟩
      rw [← range_commHom hAc]
      exact ⟨_, rfl⟩
    calc Nat.card M = Nat.card g.range := Nat.card_congr (MonoidHom.ofInjective hginj).toEquiv
      _ ≤ Nat.card (commOf φ) := Subgroup.card_le_of_le hle
      _ = 3 := hφ.1.2
  have heq : ∀ y : A, (y : G) ∈ kOf A φ → orderOf (y : G) = 3 → Subgroup.zpowers y = M :=
    fun y hy hy3 => Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy)
      (by rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, hy3]; exact hcardM)
  have hc : commOf φ = commOf ψ := by rw [hcz, hcz', heq z hzK hz3, heq z' hzK' hz3']
  exact eq_of_fixed_eq_of_commOf_eq hAc hA3 hφ.1.1 hψ.1.1 hfix hc

theorem card_eq_three_mul_inf_centralizer_kOf [Finite G] (h222 : Item222)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A)
    {φ : MulAut A} (hφ : φ ∈ dStar A) :
    Nat.card A = 3 * Nat.card (A ⊓ Subgroup.centralizer (kOf A φ : Set G) : Subgroup G) := by
  have hAc : ∀ a b : A, a * b = b * a := hpair.mem_S.1.1.1.is_comm.comm
  rw [inf_centralizer_kOf_eq h222 hpair hK hφ, fixedInG,
    Subgroup.card_map_of_injective A.subtype_injective]
  exact card_eq_three_mul_card_fixed hAc hφ.1

theorem eq_sup_inf_centralizer_kOf [Finite G] (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A) {φ : MulAut A}
    (hφ : φ ∈ dStar A) :
    A = (A ⊓ Subgroup.centralizer (kOf A φ : Set G)) ⊔ (A ⊓ kOf A φ) := by
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hA3 : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hAe.2 a a.2)
  have hφφ := apply_apply_of_orderOf_eq_two hφ.1.1
  refine le_antisymm (fun a ha => ?_) (sup_le inf_le_left inf_le_left)
  set a' : A := ⟨a, ha⟩
  have hb : ((a' * φ a' : A) : G) ∈ A ⊓ Subgroup.centralizer (kOf A φ : Set G) := by
    rw [inf_centralizer_kOf_eq h222 hpair hK hφ]
    refine ⟨a' * φ a', ?_, rfl⟩
    rw [SetLike.mem_coe, mem_fixedSubgroupOf, map_mul, hφφ]
    exact hAc _ _
  have hw : (((φ a')⁻¹ * a' : A) : G) ∈ A ⊓ kOf A φ := by
    refine ⟨Subtype.prop _, map_commOf_le_kOf h222 hpair hK hφ ⟨(φ a')⁻¹ * a', ?_, rfl⟩⟩
    have h := (commOf φ).inv_mem (mem_commOf φ a')
    rwa [mul_inv_rev, inv_inv] at h
  have ha' := congrArg Subtype.val (eq_sq_of_exponent_three hA3 φ a')
  change a = _ at ha'
  rw [ha', Subgroup.coe_pow, Subgroup.coe_mul]
  exact Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hb)
    (Subgroup.mem_sup_right hw)) 2

theorem centralizer_sup (X Y : Subgroup G) :
    Subgroup.centralizer ((X ⊔ Y : Subgroup G) : Set G) =
      Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer (Y : Set G) := by
  apply le_antisymm
  · exact le_inf (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right))
  · intro g hg
    have hle : X ⊔ Y ≤ Subgroup.centralizer ({g} : Set G) :=
      sup_le (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hg.1 x hx))
        (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hg.2 y hy))
    exact Subgroup.mem_centralizer_iff.mpr fun h hh =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle hh)

theorem card_eq_nine_mul_inf_centralizer_kOf [Finite G] (h222 : Item222)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A)
    {φ ψ : MulAut A} (hφ : φ ∈ dStar A) (hψ : ψ ∈ dStar A) (hne : φ ≠ ψ) :
    Nat.card A =
      9 * Nat.card (A ⊓ Subgroup.centralizer ((kOf A φ ⊔ kOf A ψ : Subgroup G) : Set G) :
        Subgroup G) := by
  have hAc : ∀ a b : A, a * b = b * a := hpair.mem_S.1.1.1.is_comm.comm
  have hinf : A ⊓ Subgroup.centralizer ((kOf A φ ⊔ kOf A ψ : Subgroup G) : Set G) =
      (fixedSubgroupOf φ ⊓ fixedSubgroupOf ψ).map A.subtype := by
    rw [centralizer_sup, Subgroup.map_inf_eq _ _ _ A.subtype_injective]
    change _ = fixedInG A φ ⊓ fixedInG A ψ
    rw [← inf_centralizer_kOf_eq h222 hpair hK hφ, ← inf_centralizer_kOf_eq h222 hpair hK hψ]
    ext x
    simp only [Subgroup.mem_inf]
    tauto
  rw [hinf, Subgroup.card_map_of_injective A.subtype_injective]
  exact card_eq_nine_mul_card_inf hAc hφ.1 hψ.1 (fixedSubgroupOf_ne_of_ne h222 hpair hK hφ hψ hne)

end CFSG.RankThree.PartTwo.Sec21
