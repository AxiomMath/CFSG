module

public import CFSG.Assembly.Defs

public section

namespace CFSG.StandardType.GGSixE6Two

section Schur

variable {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem rep_eq_one_of_central_pow_two [Finite W] {σ : Representation (ZMod 2) G W}
    (hirr : σ.IsIrreducible) {z : G} (hz : z ∈ Subgroup.center G) {k : ℕ}
    (hk : σ (z ^ 2 ^ k) = 1) : σ z = 1 := by
  haveI : Nontrivial W := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    haveI := h
    haveI : Subsingleton (Subrepresentation σ) :=
      ⟨fun S T => Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)⟩
    obtain ⟨x, y, hxy⟩ := hirr.exists_pair_ne
    exact hxy (Subsingleton.elim x y)
  haveI hchar : CharP (Module.End (ZMod 2) W) 2 := by
    refine CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero ?_
    ext w
    simp [two_smul, ZModModule.add_self]
  let N : Module.End (ZMod 2) W := σ z - 1
  have hN : ∀ w, N w = σ z w - w := fun w => by simp [N]
  have hker_inv : ∀ g, ∀ w ∈ N.ker, σ g w ∈ N.ker := by
    intro g w hw
    rw [LinearMap.mem_ker] at hw ⊢
    have hcg : σ z * σ g = σ g * σ z := by
      calc σ z * σ g = σ (z * g) := (map_mul σ z g).symm
        _ = σ (g * z) := by rw [(Subgroup.mem_center_iff.mp hz g).symm]
        _ = σ g * σ z := map_mul σ g z
    have hcw : σ z (σ g w) = σ g (σ z w) := by
      simpa [Module.End.mul_apply] using DFunLike.congr_fun hcg w
    calc N (σ g w) = σ g (N w) := by rw [hN, hN, map_sub, hcw]
      _ = σ g 0 := by rw [hw]
      _ = 0 := map_zero _
  let S : Subrepresentation σ :=
    { toSubmodule := N.ker
      apply_mem_toSubmodule := fun g w hw => hker_inv g w hw }
  rcases hirr.eq_bot_or_eq_top S with hS | hS
  · have hbot : N.ker = ⊥ := by
      have h := congrArg Subrepresentation.toSubmodule hS
      rw [show S.toSubmodule = N.ker from rfl] at h
      rwa [show (⊥ : Subrepresentation σ).toSubmodule = (⊥ : Submodule (ZMod 2) W) from rfl] at h
    have hinj : Function.Injective N := LinearMap.ker_eq_bot.mp hbot
    have hpow : N ^ (2 ^ k) = 0 := by
      have h1 : (σ z) ^ (2 ^ k) = 1 := by rw [← map_pow, hk]
      calc N ^ (2 ^ k) = (σ z) ^ (2 ^ k) - 1 ^ (2 ^ k) :=
            sub_pow_char_pow_of_commute 2 k (Commute.one_right (σ z))
        _ = 0 := by rw [h1]; simp
    have hN0 : N = 0 := by
      apply LinearMap.ext
      intro w
      have hfun : (⇑N)^[2 ^ k] = 0 := by
        rw [← Module.End.coe_pow N (2 ^ k), hpow]
        rfl
      have h2 : (⇑N)^[2 ^ k] (N w) = (⇑N)^[2 ^ k] 0 := by rw [hfun]; rfl
      exact hinj.iterate (2 ^ k) h2
    have htop : S = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      show N.ker = ⊤
      rw [hN0, LinearMap.ker_zero]
    exact (bot_ne_top (hS.symm.trans htop)).elim
  · have htop : N.ker = ⊤ := by
      have h := congrArg Subrepresentation.toSubmodule hS
      rw [show S.toSubmodule = N.ker from rfl] at h
      rwa [show (⊤ : Subrepresentation σ).toSubmodule = (⊤ : Submodule (ZMod 2) W) from rfl] at h
    have hN0 : N = 0 := LinearMap.ker_eq_top.mp htop
    exact sub_eq_zero.mp (show σ z - 1 = 0 from hN0)

end Schur

section Quasisimple

variable {G : Type} [Group G]

theorem le_center_of_normal_ne_top (hq : CFSG.Assembly.IsQuasisimple G) {K : Subgroup G} [K.Normal]
    (hK : K ≠ ⊤) : K ≤ Subgroup.center G := by
  let Z := Subgroup.center G
  let q := QuotientGroup.mk' Z
  haveI : IsSimpleGroup (G ⧸ Z) := hq.2
  haveI hnormal : (K.map q).Normal :=
    Subgroup.Normal.map (inferInstance : K.Normal) q (QuotientGroup.mk'_surjective Z)
  rcases Subgroup.Normal.eq_bot_or_eq_top (K.map q) with hbot | htop
  · intro k hk
    have hmem : q k ∈ (⊥ : Subgroup (G ⧸ Z)) := hbot ▸ Subgroup.mem_map_of_mem q hk
    rw [Subgroup.mem_bot] at hmem
    change k ∈ Z
    rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker]
    exact hmem
  · exfalso
    have hKZ : K ⊔ Z = ⊤ := by
      have h := QuotientGroup.comap_map_mk' Z K
      rw [htop, Subgroup.comap_top] at h
      simpa [sup_comm] using h.symm
    have hle : commutator G ≤ K := by
      have hG : commutator G = ⁅K ⊔ Z, K ⊔ Z⁆ := by
        change ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⁅K ⊔ Z, K ⊔ Z⁆
        rw [← hKZ]
      rw [hG, Subgroup.commutator_sup_right, Subgroup.commutator_sup_left,
        Subgroup.commutator_center_right, Subgroup.commutator_center_left]
      simp [Subgroup.commutator_le_self]
    have htopK : (⊤ : Subgroup G) ≤ K := by rw [← hq.1]; exact hle
    exact hK (le_antisymm le_top htopK)

theorem commutator_quotient_eq_top (h : commutator G = ⊤) (K : Subgroup G) [K.Normal] :
    commutator (G ⧸ K) = ⊤ := by
  haveI : Group.IsPerfect G := Group.isPerfect_def.mpr h
  exact Group.IsPerfect.commutator_eq_top

theorem exists_mem_center_of_mem_center_quotient (hq : CFSG.Assembly.IsQuasisimple G)
    {K : Subgroup G} [K.Normal] (hK : K ≤ Subgroup.center G) {z : G ⧸ K}
    (hz : z ∈ Subgroup.center (G ⧸ K)) :
    ∃ g ∈ Subgroup.center G, (g : G ⧸ K) = z := by
  haveI : Group.IsPerfect G := Group.isPerfect_def.mpr hq.1
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K z
  refine ⟨g, ?_, ?_⟩
  · have hgz : (QuotientGroup.mk' (Subgroup.center G)) g ∈
        Subgroup.center (G ⧸ Subgroup.center G) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) y
      rw [← map_mul, ← map_mul]
      simp only [QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq]
      have hcomm : (QuotientGroup.mk' K) (h * g) = (QuotientGroup.mk' K) (g * h) := by
        have hc := (Subgroup.mem_center_iff.mp hz) (QuotientGroup.mk' K h)
        rwa [← map_mul, ← map_mul] at hc
      have hcomm' : ((h * g : G) : G ⧸ K) = ((g * h : G) : G ⧸ K) := by
        simpa only [QuotientGroup.mk'_apply] using hcomm
      exact hK (QuotientGroup.eq.mp hcomm')
    rw [Group.IsPerfect.center_quotient_center_eq_bot G] at hgz
    rw [Subgroup.mem_bot] at hgz
    rw [← QuotientGroup.ker_mk' (Subgroup.center G), MonoidHom.mem_ker]
    exact hgz
  · exact (QuotientGroup.mk'_apply K g).symm

theorem nonempty_quotient_center_mulEquiv (hq : CFSG.Assembly.IsQuasisimple G)
    {K : Subgroup G} [K.Normal] (hK : K ≤ Subgroup.center G) :
    Nonempty (((G ⧸ K) ⧸ Subgroup.center (G ⧸ K)) ≃* (G ⧸ Subgroup.center G)) := by
  have hcenter : Subgroup.center (G ⧸ K) = (Subgroup.center G).map (QuotientGroup.mk' K) := by
    apply le_antisymm
    · intro z hz
      obtain ⟨g, hg, hgz⟩ := exists_mem_center_of_mem_center_quotient hq hK hz
      exact Subgroup.mem_map.mpr ⟨g, hg, by rw [QuotientGroup.mk'_apply]; exact hgz⟩
    · rintro z ⟨g, hg, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective K y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hg h]
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hcenter).trans ?_⟩
  exact QuotientGroup.quotientQuotientEquivQuotient K (Subgroup.center G) hK

end Quasisimple

end CFSG.StandardType.GGSixE6Two
