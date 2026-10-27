module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429CfgForward
public import CFSG.RankThree.PartTwo.Sec4.RonanK429Rows

public section

namespace CFSG.RankThree.PartTwo.Sec19.Census1915ImageProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec4.RonanK429

section Cores

theorem inf_eq_bot_of_center_quot_eq_bot {Γ : Type} [Group Γ] [Finite Γ] {K P : Subgroup Γ}
    (hZ : Subgroup.center (K ⧸ CFSG.pCore 2 K) = ⊥) (hP : P ≤ Subgroup.center Γ)
    (hP3 : IsPGroup 3 P) : K ⊓ P = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  set k : K := ⟨x, hx.1⟩
  have hkZ : k ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hP hx.2) (y : Γ))
  have hkbar : (k : K ⧸ CFSG.pCore 2 K) ∈ Subgroup.center (K ⧸ CFSG.pCore 2 K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    induction y using QuotientGroup.induction_on with
    | H y =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hkZ y]
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hkbar
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 K)) ⟨k, hkbar⟩
  obtain ⟨b, hb⟩ := hP3 ⟨x, hx.2⟩
  have ha' : x ^ 2 ^ a = 1 := by
    have := congrArg (fun w : CFSG.pCore 2 K => ((w : K) : Γ)) ha
    simpa using this
  have hb' : x ^ 3 ^ b = 1 := by
    have := congrArg (fun w : P => (w : Γ)) hb
    simpa using this
  have hcop : Nat.Coprime (2 ^ a) (3 ^ b) := Nat.Coprime.pow a b (by norm_num)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one ha')
    (orderOf_dvd_of_pow_eq_one hb'))

theorem pCore_eq_bot_of_isSubnormal {Y : Type} [Group Y] [Finite Y] {W : Subgroup Y}
    (hW : W.IsSubnormal) (h : CFSG.pCore 2 Y = ⊥) : CFSG.pCore 2 W = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Late.pCoreOf_le_pCore_of_isSubnormal 2 hW
  rw [h] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ W.subtype_injective).mp (le_bot_iff.mp h1)

end Cores

section Surj

variable {L J : Type} [Group L] [Group J] [Finite J]

theorem comap_pCore_eq_of_surjective_of_perfect (ψ : L →* J) (hψ : Function.Surjective ψ)
    (hJp : Group.IsPerfect J) [Nontrivial J] (hL : IsSimpleGroup (L ⧸ CFSG.pCore 2 L)) :
    (CFSG.pCore 2 J).comap ψ = CFSG.pCore 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := (CFSG.pCore 2 J).comap ψ with hMdef
  have hle : CFSG.pCore 2 L ≤ M := by
    rw [hMdef, ← Subgroup.map_le_iff_le_comap]
    have hN : ((CFSG.pCore 2 L).map ψ).Normal := Subgroup.Normal.map inferInstance ψ hψ
    have hP : IsPGroup 2 ((CFSG.pCore 2 L).map ψ) := CFSG.pCore_isPGroup.map ψ
    exact le_sSup ⟨hN, hP⟩
  have hMn : M.Normal := Subgroup.Normal.comap inferInstance ψ
  have hMm : (M.map (QuotientGroup.mk' (CFSG.pCore 2 L))).Normal :=
    Subgroup.Normal.map hMn _ (QuotientGroup.mk'_surjective _)
  rcases hL.eq_bot_or_eq_top_of_normal (M.map (QuotientGroup.mk' (CFSG.pCore 2 L))) with h | h
  · refine le_antisymm (fun x hx => ?_) hle
    have hx' : QuotientGroup.mk' (CFSG.pCore 2 L) x ∈
        M.map (QuotientGroup.mk' (CFSG.pCore 2 L)) := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
    exact hx'
  · exfalso
    have hMtop : M = ⊤ := by
      have h1 := QuotientGroup.comap_map_mk' (CFSG.pCore 2 L) M
      rw [h, Subgroup.comap_top, sup_eq_right.mpr hle] at h1
      exact h1.symm
    have hJtop : CFSG.pCore 2 J = ⊤ := by
      rw [eq_top_iff]
      intro y _
      obtain ⟨x, rfl⟩ := hψ y
      have hx : x ∈ M := hMtop ▸ Subgroup.mem_top x
      exact hx
    have hJ2 : IsPGroup 2 J := by
      intro y
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := J)) ⟨y, hJtop ▸ Subgroup.mem_top y⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    haveI := hJp
    exact Group.IsPerfect.not_isNilpotent J hJ2.isNilpotent

noncomputable def quotientPCoreEquivOfPerfect (ψ : L →* J) (hψ : Function.Surjective ψ)
    (hJp : Group.IsPerfect J) [Nontrivial J] (hL : IsSimpleGroup (L ⧸ CFSG.pCore 2 L)) :
    L ⧸ CFSG.pCore 2 L ≃* J ⧸ CFSG.pCore 2 J :=
  (QuotientGroup.quotientMulEquivOfEq (by
      rw [← comap_pCore_eq_of_surjective_of_perfect ψ hψ hJp hL, ← MonoidHom.comap_ker,
        QuotientGroup.ker_mk'])).trans
    (QuotientGroup.quotientKerEquivOfSurjective ((QuotientGroup.mk' (CFSG.pCore 2 J)).comp ψ)
      ((QuotientGroup.mk'_surjective _).comp hψ))

end Surj

section Cfg

variable {G : Type} [Group G] [Finite G]

theorem cfgS429_of_perfect {A : Subgroup G} (hA : Late.IsE27 A) {c : G} (hc : c ∈ A)
    {L : Subgroup G} (hLp : Group.IsPerfect L) (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hAC : A ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hLc : ¬ L ≤ Subgroup.centralizer {c})
    {K' : Subgroup G} (hK'M : K' ≤ L ⊓ Subgroup.centralizer {c}) (hK'p : Group.IsPerfect K')
    (hK'sn : (K'.subgroupOf (L ⊓ Subgroup.centralizer {c})).IsSubnormal)
    (hK'type : IsType429 (K' ⧸ CFSG.pCore 2 K')) (hAK' : A ≤ Subgroup.normalizer (K' : Set G))
    (hinf : K'.subgroupOf L ⊓ Subgroup.center L = ⊥)
    (hfaith : ∀ a ∈ A, (∀ k ∈ K', a * k * a⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K') →
      a ∈ Subgroup.zpowers c) :
    CfgS429 (L ⧸ Subgroup.center L) (aBar hAN) (descAut L ⟨c, hAN hc⟩)
      ((K'.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center L))) := by
  have hK'L : K' ≤ L := hK'M.trans inf_le_left
  set K₁ : Subgroup L := K'.subgroupOf L with hK₁
  set Kb : Subgroup (L ⧸ Subgroup.center L) := K₁.map (QuotientGroup.mk' (Subgroup.center L))
    with hKb
  have hinj := mk_comp_injective_of_inf_eq_bot hinf
  refine
    { isE27 := isE27_aBar hLp hAN hAC hA
      mem := descAut_mem_aBar hAN hc
      ne_one := ?_
      le_autFix := map_le_autFix (hAN hc) (hK'M.trans inf_le_right)
      isSubnormal := isSubnormal_bar (hAN hc) hK'M hK'sn
      isPerfect := ?_
      map_mem := fun x hx y hy => descAut_mem_bar hK'L hAN hAK' hx hy
      isType := isType429_of_mulEquiv (quotPCoreTwoCongr (equivBar hK'L hinf)).symm hK'type
      faithful := ?_ }
  ·
    intro h1
    rw [descAut_eq_one_iff hLp] at h1
    apply hLc
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp h1 l hl)
  ·
    haveI : Group.IsPerfect K' := hK'p
    haveI : Group.IsPerfect K₁ := Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hK'L).symm.toMonoidHom) (MulEquiv.surjective _)
    exact Group.IsPerfect.map _
  ·
    intro x hx hxK
    obtain ⟨a, ha, rfl⟩ := (mem_aBar_iff hAN).mp hx
    have haK' : ∀ k ∈ K', a * k * a⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K' := by
      intro k hk
      set l : L := ⟨k, hK'L hk⟩ with hl
      have hlK₁ : l ∈ K₁ := hk
      have hak : a * k * a⁻¹ ∈ K' := (Subgroup.mem_normalizer_iff.mp (hAK' ha) k).mp hk
      set l' : L := L.normalizerMonoidHom ⟨a, hAN ha⟩ l * l⁻¹ with hl'
      have hl'K₁ : l' ∈ K₁ := by
        change a * k * a⁻¹ * k⁻¹ ∈ K'
        exact Subgroup.mul_mem _ hak (Subgroup.inv_mem _ hk)
      have h1 := hxK (l : L ⧸ Subgroup.center L) ⟨l, hlK₁, rfl⟩
      have h2 : QuotientGroup.mk' (Subgroup.center L) l' ∈ CFSG.Open.pCoreOf 2 Kb := h1
      rw [map_mem_pCoreOf_map_iff 2 _ hinj hl'K₁] at h2
      have h3 : L.subtype l' ∈ CFSG.Open.pCoreOf 2 (K₁.map L.subtype) := by
        rw [pCoreOf_map_of_injective 2 L.subtype (L.subtype_injective.comp K₁.subtype_injective)]
        exact ⟨l', h2, rfl⟩
      rw [hK₁, Subgroup.map_subgroupOf_eq_of_le hK'L] at h3
      exact h3
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hfaith a ha haK')
    have hN : (⟨a, hAN ha⟩ : Subgroup.normalizer (L : Set G)) =
        (⟨c, hAN hc⟩ : Subgroup.normalizer (L : Set G)) ^ m :=
      Subtype.ext (by rw [Subgroup.coe_zpow]; exact hm.symm)
    rw [hN, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ m

end Cfg

end CFSG.RankThree.PartTwo.Sec19.Census1915ImageProof
