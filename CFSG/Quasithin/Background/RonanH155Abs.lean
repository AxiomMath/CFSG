module

public import CFSG.GF2Type.Aschbacher1976Full.HSGL3
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.Quasithin.RonanH155

theorem ronanH155_pCore_le_ker_GL32 {G : Type*} [Group G] [Finite G]
    (π : G →* GL (Fin 3) (ZMod 2)) (hsurj : Function.Surjective π) :
    CFSG.pCore 2 G ≤ π.ker := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup (GL (Fin 3) (ZMod 2)) :=
    CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
  have hNn : (CFSG.pCore 2 G).Normal := CFSG.pCore_normal
  have hNp : IsPGroup 2 (CFSG.pCore 2 G) := CFSG.pCore_isPGroup
  haveI : ((CFSG.pCore 2 G).map π).Normal := Subgroup.Normal.map hNn π hsurj
  have hM : IsPGroup 2 ((CFSG.pCore 2 G).map π) := hNp.map π
  intro g hg
  rw [MonoidHom.mem_ker]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 G).map π) with hb | ht
  · have hmem : π g ∈ (CFSG.pCore 2 G).map π := ⟨g, hg, rfl⟩
    rw [hb, Subgroup.mem_bot] at hmem
    exact hmem
  · exfalso
    have hcard : Nat.card ((CFSG.pCore 2 G).map π) = 168 := by
      rw [ht, Subgroup.card_top, CFSG.ComponentClassification.GHarris.card_GL32_gh]
    obtain ⟨k, hk⟩ := hM.exists_card_eq
    have h3 : 3 ∣ 2 ^ k := by
      rw [← hk, hcard]
      norm_num
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at h32

theorem ronanH155_alt3_core {G : Type*} [Group G] [Finite G] {W : Type*} [CommGroup W]
    (hW : Nat.card W = 8) (hsq : ∀ w : W, w * w = 1)
    (A C : Subgroup G) (hAC : A ≤ C) (hA : Nat.card A = 16)
    (ψ : ↥C →* MulAut W) (hsurj : Function.Surjective ψ) (hker : ψ.ker = A.subgroupOf C) :
    CFSG.Open.pCoreOf 2 C = A ∧
      ∃ π : ↥C →* GL (Fin 3) (ZMod 2), Function.Surjective π ∧ π.ker = A.subgroupOf C := by
  haveI : Finite W := Nat.finite_of_card_ne_zero (by rw [hW]; norm_num)
  obtain ⟨f⟩ := CFSG.GF2Type.Aschbacher1976Full.HS.nonempty_mulAut_mulEquiv_GL3 hW
    (fun a b => mul_comm a b) hsq
  have hπsurj : Function.Surjective (f.toMonoidHom.comp ψ) := by
    intro y
    obtain ⟨a, ha⟩ := f.surjective y
    obtain ⟨b, hb⟩ := hsurj a
    exact ⟨b, by show f (ψ b) = y; rw [hb]; exact ha⟩
  have hkerπ : (f.toMonoidHom.comp ψ).ker = A.subgroupOf C := by
    rw [← hker]
    exact MonoidHom.ker_comp_of_injective ψ f.toMonoidHom f.injective
  have hle1 : CFSG.pCore 2 ↥C ≤ (f.toMonoidHom.comp ψ).ker :=
    ronanH155_pCore_le_ker_GL32 _ hπsurj
  have hcardA : Nat.card (A.subgroupOf C) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv, hA]
  have hA2 : IsPGroup 2 (A.subgroupOf C) :=
    IsPGroup.of_card (n := 4) (hcardA.trans (by norm_num))
  have hnorm : (A.subgroupOf C).Normal := by
    rw [← hkerπ]
    infer_instance
  have hmem : A.subgroupOf C ∈ {K : Subgroup ↥C | K.Normal ∧ IsPGroup 2 K} := ⟨hnorm, hA2⟩
  have hle2 : A.subgroupOf C ≤ CFSG.pCore 2 ↥C := le_sSup hmem
  have heq : CFSG.pCore 2 ↥C = A.subgroupOf C :=
    le_antisymm (hle1.trans (le_of_eq hkerπ)) hle2
  refine ⟨?_, f.toMonoidHom.comp ψ, hπsurj, hkerπ⟩
  rw [CFSG.Open.pCoreOf, heq, Subgroup.map_subgroupOf_eq_of_le hAC]

theorem alt3_abstract {G : Type*} [Group G] [Finite G] {W : Type*} [CommGroup W]
    (hW : Nat.card W = 8) (hsq : ∀ w : W, w * w = 1)
    (A N C : Subgroup G) (hAN : A ≤ N) (hNC : N ≤ C) (hA : Nat.card A = 16)
    (hC : Nat.card C ≤ 2688) (ψ : ↥N →* MulAut W)
    (hψA : ∀ a : ↥N, (a : G) ∈ A → ψ a = 1)
    (h7 : ∃ h : ↥N, ψ h ^ 7 = 1 ∧ ψ h ≠ 1) (h2 : ∃ y : ↥N, ψ y ^ 2 = 1 ∧ ψ y ≠ 1) :
    CFSG.Open.pCoreOf 2 C = A ∧
      ∃ π : ↥C →* GL (Fin 3) (ZMod 2), Function.Surjective π ∧ π.ker = A.subgroupOf C := by
  haveI : Finite W := Nat.finite_of_card_ne_zero (by rw [hW]; norm_num)
  have hcomm : ∀ a b : W, a * b = b * a := fun a b => mul_comm a b
  have h14 : 14 ∣ Nat.card ψ.range := by
    obtain ⟨h, hh7, hh1⟩ := h7
    obtain ⟨y, hy2, hy1⟩ := h2
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hmemh : ψ h ∈ ψ.range := MonoidHom.mem_range.mpr ⟨h, rfl⟩
    have hmemy : ψ y ∈ ψ.range := MonoidHom.mem_range.mpr ⟨y, rfl⟩
    have d7 : orderOf (⟨ψ h, hmemh⟩ : ↥ψ.range) ∣ Nat.card ψ.range :=
      orderOf_dvd_natCard _
    have d2 : orderOf (⟨ψ y, hmemy⟩ : ↥ψ.range) ∣ Nat.card ψ.range :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, orderOf_eq_prime hh7 hh1] at d7
    rw [Subgroup.orderOf_mk, orderOf_eq_prime hy2 hy1] at d2
    omega
  have hX : Nat.card ψ.range = 168 :=
    CFSG.GF2Type.Aschbacher1976Full.HS.dvd_56_of_dvd_14 hW hcomm hsq ψ.range h14
  have htop : ψ.range = ⊤ :=
    CFSG.GF2Type.Aschbacher1976Full.HS.eq_top_of_dvd_14 hW hcomm hsq ψ.range h14
  have hsurj : Function.Surjective ψ := MonoidHom.range_eq_top.mp htop
  have hkerN : Nat.card ψ.ker * 168 = Nat.card N := by
    have h1 := Subgroup.card_ker_mul_card_range ψ
    rw [hX] at h1
    exact h1
  have hAN' : A.subgroupOf N ≤ ψ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    exact hψA x (Subgroup.mem_subgroupOf.mp hx)
  have hcardAN : Nat.card (A.subgroupOf N) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv, hA]
  have hker16 : 16 ≤ Nat.card ψ.ker := by
    have := Subgroup.card_le_of_le hAN'
    omega
  have hNC_card : Nat.card N ≤ Nat.card C := Subgroup.card_le_of_le hNC
  have hkerle : Nat.card ψ.ker ≤ 16 := by omega
  have hNeqC : N = C := Subgroup.eq_of_le_of_card_ge hNC (by omega)
  have hkerEq : ψ.ker = A.subgroupOf N := by
    refine (Subgroup.eq_of_le_of_card_ge hAN' ?_).symm
    omega
  have hCN : C ≤ N := le_of_eq hNeqC.symm
  have hAC : A ≤ C := hAN.trans hNC
  have hsurj' : Function.Surjective (ψ.comp (Subgroup.inclusion hCN)) := by
    intro w
    obtain ⟨n, hn⟩ := hsurj w
    exact ⟨⟨n.1, hNC n.2⟩, hn⟩
  have hker' : (ψ.comp (Subgroup.inclusion hCN)).ker = A.subgroupOf C := by
    ext x
    have h1 : x ∈ (ψ.comp (Subgroup.inclusion hCN)).ker ↔
        Subgroup.inclusion hCN x ∈ ψ.ker := MonoidHom.mem_ker
    rw [hkerEq] at h1
    exact h1.trans Iff.rfl
  exact ronanH155_alt3_core hW hsq A C hAC hA (ψ.comp (Subgroup.inclusion hCN)) hsurj' hker'

end CFSG.Quasithin.RonanH155
