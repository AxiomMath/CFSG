module

public import CFSG.LocalAnalysis.StandardType.GGE6DepCorootDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenTransfer
public import CFSG.LocalAnalysis.StandardType.GGE6DepZpowersInf
public import CFSG.LocalAnalysis.StandardType.GGE6DepNormalizerOfConj

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem ggFixedByCentres_gamma {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Bs L : Subgroup G} {x : G}
    (hBs : IsElemAbelian p Bs) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥L))
    (hBsL : ∀ b ∈ Bs, ∃ l ∈ L, ∃ k : ℕ, b = l * x ^ k) (S : Set ↥Bs)
    (hSL : ∀ c ∈ S, (c : G) ∈ L) {u : ↥Bs}
    (hu : u ∈ ggFixedByCentres p (ggAutomizer L Bs) S) :
    (ggGamma L hBsN).rangeRestrict u ∈
      ggFixedByCentres p (ggTorusAut (ggGamma L hBsN).range)
        ((ggGamma L hBsN).rangeRestrict '' S) := by
  classical
  set γ : ↥Bs →* MulAut ↥L := ggGamma L hBsN with hγ
  set A : Subgroup (MulAut ↥L) := γ.range with hA
  set π : ↥Bs →* ↥A := γ.rangeRestrict with hπ
  have hx_mem : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
    rw [hker]; exact Subgroup.mem_zpowers x
  have hxBs : x ∈ Bs := hx_mem.1
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := hx_mem.2
  have hxp : x ^ p = 1 := hBs.2 x hxBs
  have hD0 : Subgroup.zpowers x ⊓ L = ⊥ :=
    GGE6Dep.zpowers_inf_eq_bot_of_centralizer hp hxC hxp hZ
  have hVc : ∀ a b : ↥Bs, a * b = b * a := fun a b => hBs.1.is_comm.comm a b
  have hVp : ∀ v : ↥Bs, v ^ p = 1 := fun v => Subtype.ext (by simpa using hBs.2 (v : G) v.2)
  change ∀ φ' ∈ ggTorusAut A, GGIsReflection p φ' →
    (∃ c' ∈ (π '' S), GGReflCentre φ' c') → φ' (π u) = π u
  intro φ' hφ'A hφ'refl hcenter
  have hφ'aut : φ' ∈ ggAutomizer ((MulAut.conj : ↥L →* MulAut ↥L).range) A := hφ'A
  obtain ⟨g', hg'H, hg'N, hg'act⟩ := mem_ggAutomizer_iff.mp hφ'aut
  obtain ⟨n₀, hn₀⟩ := MonoidHom.mem_range.mp hg'H
  have hN : (n₀ : G) ∈ Subgroup.normalizer (Bs : Set G) :=
    GGE6Dep.mem_normalizer_of_conj_mem_normalizer_range hp hBsN hBs hker hZ hBsL n₀.2 (by
      show MulAut.conj n₀ ∈ Subgroup.normalizer (γ.range : Set (MulAut ↥L))
      rw [hn₀]; exact hg'N)
  set ψ : MulAut ↥Bs := ggConjAut Bs hN with hψ
  have hψA : ψ ∈ ggAutomizer L Bs := by
    rw [hψ]; exact ggConjAut_mem_ggAutomizer n₀.2 hN
  have hcr : ∀ v : ↥Bs, π (ψ v) = φ' (π v) := by
    intro v
    apply Subtype.ext
    have hb : (n₀ : G) * (v : G) * (n₀ : G)⁻¹ ∈ Bs :=
      (Subgroup.mem_normalizer_iff.mp hN (v : G)).mp v.2
    have hv : (ψ v : ↥Bs) = ⟨(n₀ : G) * (v : G) * (n₀ : G)⁻¹, hb⟩ := by
      apply Subtype.ext
      rw [hψ]
      exact ggConjAut_apply Bs hN v
    calc (π (ψ v) : MulAut ↥L) = γ ⟨(n₀ : G) * (v : G) * (n₀ : G)⁻¹, hb⟩ := by rw [hv]; rfl
      _ = MulAut.conj n₀ * γ v * (MulAut.conj n₀)⁻¹ := ggGamma_conj L hBsN n₀ v hb
      _ = g' * γ v * g'⁻¹ := by rw [hn₀]
      _ = g' * (π v : MulAut ↥L) * g'⁻¹ := rfl
      _ = (φ' (π v) : MulAut ↥L) := (hg'act (π v)).symm
  have hfix : ∀ v ∈ π.ker, ψ v = v := by
    intro v hv
    have hv1 : γ v = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hv)
    have hvc : (v : G) ∈ Subgroup.centralizer (L : Set G) :=
      (ggGamma_eq_one_iff L hBsN v).mp hv1
    apply Subtype.ext
    rw [hψ, ggConjAut_apply Bs hN v]
    have hcomm : (n₀ : G) * (v : G) = (v : G) * (n₀ : G) :=
      (Subgroup.mem_centralizer_iff.mp hvc) (n₀ : G) n₀.2
    rw [hcomm]
    group
  have hψ2 : ψ ^ 2 = 1 := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    have hπ2 : π ((ψ ^ 2) b) = π b := by
      have h1 : π (ψ (ψ b)) = φ' (φ' (π b)) := by rw [hcr (ψ b), hcr b]
      have h2 : φ' (φ' (π b)) = π b := by
        have := congrArg (fun f : MulAut ↥A => f (π b)) hφ'refl.1
        simpa [pow_two, MulAut.mul_apply] using this
      rw [pow_two, MulAut.mul_apply]
      exact h1.trans h2
    have hmem_ker : ((ψ ^ 2) b * b⁻¹ : ↥Bs) ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hπ2, mul_inv_cancel]
    have hmem_inf : (((ψ ^ 2) b * b⁻¹ : ↥Bs) : G) ∈
        Bs ⊓ Subgroup.centralizer (L : Set G) := by
      have h1 : γ ((ψ ^ 2) b * b⁻¹) = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp hmem_ker)
      exact ⟨((ψ ^ 2) b * b⁻¹).2, (ggGamma_eq_one_iff L hBsN _).mp h1⟩
    have hmem_x : (((ψ ^ 2) b * b⁻¹ : ↥Bs) : G) ∈ Subgroup.zpowers x := by
      rw [← hker]; exact hmem_inf
    have hmemL : (((ψ ^ 2) b * b⁻¹ : ↥Bs) : G) ∈ L := by
      have h2 : (((ψ ^ 2) b : ↥Bs) : G) = (n₀ : G) ^ 2 * (b : G) * ((n₀ : G) ^ 2)⁻¹ := by
        simpa [hψ] using ggConjAut_pow_apply Bs hN 2 b
      show (((ψ ^ 2) b : ↥Bs) : G) * (b : G)⁻¹ ∈ L
      rw [h2]
      have hn2 : (n₀ : G) ^ 2 ∈ L := Subgroup.pow_mem L n₀.2 2
      have hb2 : (b : G) * ((n₀ : G) ^ 2)⁻¹ * (b : G)⁻¹ ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp (hBsN b.2) (((n₀ : G) ^ 2)⁻¹)).mp
          (L.inv_mem hn2)
        simpa using this
      have hmul := L.mul_mem hn2 hb2
      convert hmul using 1
      group
    have hw1 : ((ψ ^ 2) b * b⁻¹ : ↥Bs) = 1 := by
      have hbot : (((ψ ^ 2) b * b⁻¹ : ↥Bs) : G) ∈ (⊥ : Subgroup G) := by
        rw [← hD0]; exact ⟨hmem_x, hmemL⟩
      exact Subtype.ext (Subgroup.mem_bot.mp hbot)
    exact mul_inv_eq_one.mp (by simpa using congrArg Subtype.val hw1)
  have hψrefl : GGIsReflection p ψ :=
    isReflection_of_quotient hp hp2 hVc hVp π (MonoidHom.rangeRestrict_surjective γ) ψ φ'
      hcr hfix (a := 1) (by simpa using hψ2) hφ'refl.1 hφ'refl.2
  obtain ⟨c', hc'mem, hφc⟩ := hcenter
  obtain ⟨c, hcS, hc'eq⟩ := hc'mem
  rw [← hc'eq] at hφc
  have hψc : GGReflCentre ψ c := by
    intro b
    have hπmem : π (ψ b * b⁻¹) ∈ Subgroup.zpowers (π c) := by
      have hthis := hφc (π b)
      rwa [show π (ψ b * b⁻¹) = φ' (π b) * (π b)⁻¹ by rw [map_mul, map_inv, hcr b]]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hπmem
    let w : ↥Bs := ψ b * b⁻¹
    let ck : ↥Bs := c ^ k
    have hwL : (w : G) ∈ L := by
      have h2 : (ψ b : G) = (n₀ : G) * (b : G) * (n₀ : G)⁻¹ := by
        rw [hψ]; exact ggConjAut_apply Bs hN b
      show (ψ b : G) * (b : G)⁻¹ ∈ L
      rw [h2]
      have hnL : (n₀ : G) ∈ L := n₀.2
      have hbnL : (b : G) * (n₀ : G)⁻¹ * (b : G)⁻¹ ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp (hBsN b.2) ((n₀ : G)⁻¹)).mp (L.inv_mem n₀.2)
        simpa using this
      have hmul := L.mul_mem hnL hbnL
      convert hmul using 1
      group
    have hckL : (ck : G) ∈ L := Subgroup.zpow_mem L (hSL c hcS) k
    have hπck : π ck = π w := by
      show π (c ^ k) = π w
      rw [map_zpow]
      exact hk
    have hker_mem : w * ck⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hπck, mul_inv_cancel]
    have hinf : ((w * ck⁻¹ : ↥Bs) : G) ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
      have h1 : γ (w * ck⁻¹) = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp hker_mem)
      exact ⟨(w * ck⁻¹).2, (ggGamma_eq_one_iff L hBsN _).mp h1⟩
    have hmemx : ((w * ck⁻¹ : ↥Bs) : G) ∈ Subgroup.zpowers x := by
      rw [← hker]; exact hinf
    have hmemL : ((w * ck⁻¹ : ↥Bs) : G) ∈ L := by
      have := L.mul_mem hwL (L.inv_mem hckL)
      simpa using this
    have hw1 : w * ck⁻¹ = 1 := by
      have hbot : ((w * ck⁻¹ : ↥Bs) : G) ∈ (⊥ : Subgroup G) := by
        rw [← hD0]; exact ⟨hmemx, hmemL⟩
      exact Subtype.ext (Subgroup.mem_bot.mp hbot)
    have hwck : w = ck := mul_inv_eq_one.mp hw1
    show w ∈ Subgroup.zpowers c
    rw [hwck]
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
  have huψ : ψ u = u := hu ψ hψA hψrefl ⟨c, hcS, hψc⟩
  have hfin := hcr u
  rw [huψ] at hfin
  exact hfin.symm

end CFSG.StandardType

end
