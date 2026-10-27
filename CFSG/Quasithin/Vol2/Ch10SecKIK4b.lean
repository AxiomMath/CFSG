module

public import CFSG.Quasithin.Vol2.Ch10SecC9S5e
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

noncomputable def quotEquiv {J : Subgroup G} (α : ↥J →* ↥(alternatingGroup (Fin 7)))
    (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥J) :
    ↥J ⧸ CFSG.pCore 2 ↥J ≃* ↥(alternatingGroup (Fin 7)) :=
  (QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hαs)

theorem nonempty_autI_equiv {J W : Subgroup G} (hW : IsElemAbelian 2 W)
    (hJN : J ≤ Subgroup.normalizer (W : Set G))
    (hCJ : J ⊓ Subgroup.centralizer (W : Set G) = pCoreOf 2 J)
    (α : ↥J →* ↥(alternatingGroup (Fin 7))) (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥J) :
    Nonempty (↥(autI hW J) ≃* ↥(alternatingGroup (Fin 7))) := by
  obtain ⟨e⟩ := nonempty_quotient_equiv hW hJN hCJ (MulEquiv.refl ↥(autI hW J))
  exact ⟨e.symm.trans (quotEquiv α hαs hαk)⟩

theorem center_autI_eq_bot {J W : Subgroup G} (hW : IsElemAbelian 2 W)
    (hJN : J ≤ Subgroup.normalizer (W : Set G))
    (hCJ : J ⊓ Subgroup.centralizer (W : Set G) = pCoreOf 2 J)
    (α : ↥J →* ↥(alternatingGroup (Fin 7))) (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥J) : Subgroup.center ↥(autI hW J) = ⊥ := by
  obtain ⟨e⟩ := nonempty_autI_equiv hW hJN hCJ α hαs hαk
  have h1 : Nat.card (Subgroup.center ↥(autI hW J)) = 1 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, center_alt7, Subgroup.card_bot]
  exact Subgroup.card_eq_one.1 h1

theorem mem_centralizer_of_commutator [Finite G] {H J W : Subgroup G} (hW : IsElemAbelian 2 W)
    (hred : IsTwoReducedIn H W) (hHJ : H ≤ Subgroup.normalizer (J : Set G))
    (h2 : ∀ h ∈ H, ∃ e : ℕ, h ^ 2 ^ e ∈ J) (hZ : Subgroup.center ↥(autI hW J) = ⊥) {h : G}
    (hh : h ∈ H) (hc : ∀ j ∈ J, ⁅h, j⁆ ∈ Subgroup.centralizer (W : Set G)) :
    h ∈ Subgroup.centralizer (W : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHN : H ≤ Subgroup.normalizer (W : Set G) := hred.2.1
  set X := autI hW H with hX
  set K := autI hW J with hK
  set C : Subgroup (MulAut (IntMod W hW)) := X ⊓ Subgroup.centralizer (K : Set _) with hC
  have hKn : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K := by
    intro x hx k hk
    obtain ⟨g, hg, rfl⟩ := (mem_autI hW).1 hx
    obtain ⟨l, hl, rfl⟩ := (mem_autI hW).1 hk
    have hgl : (g : G) * l * (g : G)⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hHJ hg) l).mp hl
    have e : convI hW g * convI hW l * (convI hW g)⁻¹ = convI hW (g * l * g⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [e]
    exact convI_mem_autI hW hgl (g * l * g⁻¹).2
  have hXC : X ≤ Subgroup.normalizer (C : Set (MulAut (IntMod W hW))) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc'
      obtain ⟨hcX, hcK⟩ := Subgroup.mem_inf.1 hc'
      refine Subgroup.mem_inf.2 ⟨X.mul_mem (X.mul_mem hx hcX) (X.inv_mem hx), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hk' : x⁻¹ * k * x⁻¹⁻¹ ∈ K := hKn _ (X.inv_mem hx) k hk
      rw [inv_inv] at hk'
      have := Subgroup.mem_centralizer_iff.mp hcK _ hk'
      calc k * (x * c * x⁻¹) = x * ((x⁻¹ * k * x) * c) * x⁻¹ := by group
        _ = x * (c * (x⁻¹ * k * x)) * x⁻¹ := by rw [this]
        _ = x * c * x⁻¹ * k := by group
    · intro hc'
      obtain ⟨hcX, hcK⟩ := Subgroup.mem_inf.1 hc'
      have hcX' := X.mul_mem (X.mul_mem (X.inv_mem hx) hcX) hx
      have e : x⁻¹ * (x * c * x⁻¹) * x = c := by group
      rw [e] at hcX'
      refine Subgroup.mem_inf.2 ⟨hcX', ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hk' : x * k * x⁻¹ ∈ K := hKn _ hx k hk
      have := Subgroup.mem_centralizer_iff.mp hcK _ hk'
      calc k * c = x⁻¹ * ((x * k * x⁻¹) * (x * c * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * c * x⁻¹) * (x * k * x⁻¹)) * x := by rw [this]
        _ = c * k := by group
  have hCp : IsPGroup 2 ↥C := by
    rintro ⟨c, hcC⟩
    obtain ⟨hcX, hcK⟩ := Subgroup.mem_inf.1 hcC
    obtain ⟨g, hg, rfl⟩ := (mem_autI hW).1 hcX
    obtain ⟨e, he⟩ := h2 g hg
    refine ⟨e, Subtype.ext ?_⟩
    have hmem : convI hW g ^ 2 ^ e ∈ K := by
      rw [← map_pow]
      exact convI_mem_autI hW he (g ^ 2 ^ e).2
    have hcen : (⟨_, hmem⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      have := Subgroup.mem_centralizer_iff.mp (Subgroup.pow_mem _ hcK (2 ^ e)) k k.2
      simpa using this
    rw [hZ, Subgroup.mem_bot] at hcen
    simpa using congrArg Subtype.val hcen
  have hCbot : C = ⊥ := by
    have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hXC hCp
    have hO2 : pCoreOf 2 (autI hW H) = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
    rwa [hX, hO2, le_bot_iff] at hle
  have hmemC : convI hW ⟨h, hHN hh⟩ ∈ C := by
    refine Subgroup.mem_inf.2 ⟨convI_mem_autI hW hh (hHN hh), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    obtain ⟨l, hl, rfl⟩ := (mem_autI hW).1 hk
    have hcl := hc l hl
    have h1 : convI hW (⟨h, hHN hh⟩ * l * (⟨h, hHN hh⟩ : Subgroup.normalizer (W : Set G))⁻¹ *
        l⁻¹) = 1 := by
      rw [convI_eq_one_iff]
      simpa [commutatorElement_def] using hcl
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have h2' := mul_inv_eq_one.mp h1
    calc convI hW l * convI hW ⟨h, hHN hh⟩
        = convI hW ⟨h, hHN hh⟩ * convI hW l * (convI hW ⟨h, hHN hh⟩)⁻¹ *
            convI hW ⟨h, hHN hh⟩ := by rw [h2']
      _ = convI hW ⟨h, hHN hh⟩ * convI hW l := by group
  rw [hCbot, Subgroup.mem_bot, convI_eq_one_iff] at hmemC
  exact hmemC

theorem commutator_le_or_eq [Finite G] {J X : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (J : Set G)) (hperf : ⁅J, J⁆ = J)
    (hsimple : IsSimpleGroup (↥J ⧸ CFSG.pCore 2 ↥J)) : ⁅J, X⁆ ≤ pCoreOf 2 J ∨ ⁅J, X⁆ = J := by
  have hNL : ⁅J, X⁆ ≤ J := Subgroup.le_normalizer_iff_commutator_le_left.mp hXN
  by_cases hNP : ⁅J, X⁆ ≤ pCoreOf 2 J
  · exact Or.inl hNP
  right
  have hN' : (⁅J, X⁆.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr
      (Subgroup.normalizer_commutator_ge_left J X)
  let Nbar : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J) :=
    (⁅J, X⁆.subgroupOf J).map (QuotientGroup.mk' (CFSG.pCore 2 ↥J))
  have hNbar : Nbar.Normal := Subgroup.Normal.map hN' _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Nbar with h | h
  · exfalso
    apply hNP
    intro x hx
    have hxL : x ∈ J := hNL hx
    have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥J)) ⟨x, hxL⟩ ∈ Nbar := ⟨⟨x, hxL⟩, hx, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact (C1Pack.coe_mem_pCoreOf_iff J ⟨x, hxL⟩).2 hmem
  · have hall : ∀ x : ↥J, ∃ n ∈ ⁅J, X⁆.subgroupOf J, ∃ p ∈ CFSG.pCore 2 ↥J, x = n * p := by
      intro x
      have hx : QuotientGroup.mk' (CFSG.pCore 2 ↥J) x ∈ Nbar := by rw [h]; trivial
      obtain ⟨n, hn, hnx⟩ := hx
      refine ⟨n, hn, n⁻¹ * x, ?_, by simp⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hnx
      exact QuotientGroup.eq.1 hnx
    have hpg : IsPGroup 2 (↥J ⧸ ⁅J, X⁆.subgroupOf J) := by
      intro y
      induction y using QuotientGroup.induction_on with
      | H x =>
        obtain ⟨n, hn, p, hp, rfl⟩ := hall x
        obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥J)) ⟨p, hp⟩
        refine ⟨k, ?_⟩
        have hp1 : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
        have hn1 : (QuotientGroup.mk n : ↥J ⧸ ⁅J, X⁆.subgroupOf J) = 1 :=
          (QuotientGroup.eq_one_iff n).2 hn
        rw [QuotientGroup.mk_mul, hn1, one_mul, ← QuotientGroup.mk_pow, hp1]
        rfl
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hnil : Group.IsNilpotent (↥J ⧸ ⁅J, X⁆.subgroupOf J) := hpg.isNilpotent
    have hperfL : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.2 hperf
    have hperfQ : Group.IsPerfect (↥J ⧸ ⁅J, X⁆.subgroupOf J) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    have hsub : Subsingleton (↥J ⧸ ⁅J, X⁆.subgroupOf J) := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      exact Group.IsPerfect.not_isNilpotent _ hnil
    refine le_antisymm hNL fun x hx => ?_
    have h1 : (QuotientGroup.mk (⟨x, hx⟩ : ↥J) : ↥J ⧸ ⁅J, X⁆.subgroupOf J) = 1 :=
      Subsingleton.elim _ _
    exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)

theorem commutator_thompsonJ_eq [Finite G] {H R J V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hred : IsTwoReducedIn H V) (hRH : R ≤ H) (hHJ : H ≤ Subgroup.normalizer (J : Set G))
    (h2 : ∀ h ∈ H, ∃ e : ℕ, h ^ 2 ^ e ∈ J) (hZ : Subgroup.center ↥(autI hV J) = ⊥)
    (hO : pCoreOf 2 J ≤ Subgroup.centralizer (V : Set G)) (hperf : ⁅J, J⁆ = J)
    (hsimple : IsSimpleGroup (↥J ⧸ CFSG.pCore 2 ↥J))
    (hJR : ¬ thompsonJ R ≤ Subgroup.centralizer (V : Set G)) : J = ⁅J, thompsonJ R⁆ := by
  have hJS : thompsonJ R ≤ R := iSup₂_le fun _ hA => hA.1
  rcases commutator_le_or_eq ((hJS.trans hRH).trans hHJ) hperf hsimple with h | h
  · exfalso
    apply hJR
    intro x hx
    refine mem_centralizer_of_commutator hV hred hHJ h2 hZ (hRH (hJS hx)) fun j hj => hO (h ?_)
    have := Subgroup.commutator_mem_commutator hj hx
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ this
  · exact h.symm

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
