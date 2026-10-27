module

public import CFSG.RankThree.PartOne.HESS.Node
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.RankThree.PartOne.HESS

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.RankThree.PartOne.N143
open CFSG.RankThree.PartOne.KFOUT3 (SL3 Tor rt permSL IsZeta diagSL tSep)

section Aux

variable {G : Type} [Group G]

theorem piAut_pow {A : Subgroup G} {g : G} (hg : g ∈ torusNormalizer A) (k : ℕ) :
    piAut A (g ^ k) = piAut A g ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, piAut_one]
  | succ k ih => rw [pow_succ, piAut_mul ((torusNormalizer A).pow_mem hg k) hg, ih, pow_succ]

end Aux

section A0

variable {G : Type} [Group G] {p : ℕ} {A J : Subgroup G} {K : Type} [Field K] {ρ : SL3 K →* G}

theorem tSep01_zero (ζ : Kˣ) : tSep ζ 0 1 0 = ζ := KFU.torusElt_apply_left (by decide) ζ
theorem tSep01_one (ζ : Kˣ) : tSep ζ 0 1 1 = ζ⁻¹ := KFU.torusElt_apply_right (by decide) ζ
theorem tSep01_two (ζ : Kˣ) : tSep ζ 0 1 2 = 1 := KFU.torusElt_apply_other (by decide) (by decide) ζ

theorem tSep01_prod (ζ : Kˣ) : ∏ k, tSep ζ 0 1 k = 1 := KFU.prod_torusElt 0 1 ζ

theorem tSep01_pow {ζ : Kˣ} (hζ : IsZeta p ζ) : ∀ i, tSep ζ 0 1 i ^ p = 1 := fun k =>
  (KFU.torusElt_mem (by decide : (0 : Fin 3) ≠ 1) hζ.pow :
    KFU.torusElt 0 1 ζ ∈ KFU.torusVec p 3 K).1 k

theorem orderOf_a0 (hp : p.Prime) (hρ : IsPSL3Cover p A J ρ) {ζ : Kˣ} (hζ : IsZeta p ζ) :
    orderOf (ρ (diagSL (tSep ζ 0 1) (tSep01_prod ζ))) = p := by
  have hw : diagSL (tSep ζ 0 1) (tSep01_prod ζ) ∈ Tor p K := KFOUT3.tSep_mem hζ (by decide)
  have : Fact p.Prime := ⟨hp⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, Tor_pow_eq_one hw, map_one]
  · intro h
    have h1 := hρ.eq_of_map_eq hp (Tor_pow_eq_one hw) (one_pow p) (h.trans (map_one ρ).symm)
    have h2 := congrArg (fun y : SL3 K => KFOUT3.ent y 0 0) h1
    simp only [KFOUT3.diagSL_apply, ↓reduceIte, tSep01_zero] at h2
    have h3 : (ζ : K) = 1 := by simpa [KFOUT3.ent] using h2
    have hz1 : ζ = 1 := Units.ext (by simpa using h3)
    apply hζ.sq
    rw [hz1, one_pow]

theorem actsBy_swap_inv {m : SL3 K} {ζ : Kˣ} (hζ : IsZeta p ζ) (hm : ActsBy p m (Equiv.swap 0 1)) :
    m * diagSL (tSep ζ 0 1) (tSep01_prod ζ) * m⁻¹ = (diagSL (tSep ζ 0 1) (tSep01_prod ζ))⁻¹ := by
  rw [hm _ (tSep01_prod ζ) (tSep01_pow hζ), diagSL_inv]
  refine diagSL_congr ?_ _ _
  funext k
  fin_cases k
  · simp [permVec, tSep01_zero, tSep01_one]
  · simp [permVec, tSep01_zero, tSep01_one]
  · simp [permVec, tSep01_two, swap01_two]

end A0

section NoSwapLine

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A J : Subgroup G} {c : G} {K : Type} [Field K]
  [Finite K] [CharP K 2] {ρ : SL3 K →* G} {f : ℕ}

theorem LineHyp.no_swap (hL : LineHyp p A c J f ρ) (hodd : 2 ^ f % 3 = 2) {i j : Fin 3} (hij : i ≠ j)
    (hmoved : Nat.card (autMovedInG A (nodeOf A ρ i j)) = p) {g : G} (hg : g ∈ torusNormalizer A)
    (hgK : conjBy g (Kof A J (nodeOf A ρ i j)) = Kof A J (nodeOf A ρ i j))
    (hgfix : piAut A g * nodeOf A ρ i j * (piAut A g)⁻¹ = nodeOf A ρ i j)
    (hg3 : piAut A g ^ 3 = 1) : conjBy g (rootG ρ hij) ≠ rootG ρ hij.symm := by
  intro hswap
  have hp := hL.prime
  have hp5 := Sec12Three.five_le hL.good.hyp
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := hL.exists_zeta
  obtain ⟨τ, hτ0, hτ1⟩ := exists_perm_zero_one i j hij
  set ρ' := ρ.comp (MulAut.conj (permSL τ)).toMonoidHom with hρ'
  have hρ'c : IsPSL3Cover p A J ρ' := hL.cover.conjPerm τ
  set B := blkφ ρ' with hB
  have hinj : Function.Injective B := blkφ_injective hρ'c
  have hker : Kof A J (nodeOf A ρ i j) = B.range := hL.kof_nodeOf hτ0 hτ1
  have hv0 := tSep01_prod ζ
  set d₀ : SL3 K := diagSL (tSep ζ 0 1) hv0 with hd₀
  set a₀ : G := B (hmat ζ) with ha₀
  have ha₀ρ : a₀ = ρ' d₀ := by rw [ha₀, hB, blkφ_apply, blkSL_hmat ζ hv0]
  have hd₀Tor : d₀ ∈ Tor p K := KFOUT3.tSep_mem hζ (by decide)
  have ha₀A : a₀ ∈ A := by rw [ha₀ρ]; exact hρ'c.map_mem_A hd₀Tor
  have hord : orderOf a₀ = p := by rw [ha₀ρ]; exact orderOf_a0 hp hρ'c hζ
  set t := nodeOf A ρ i j with ht
  have hxN : ρ (permSL (Equiv.swap i j)) ∈ torusNormalizer A := hL.permSL_mem_normalizer _
  set m : SL3 K := (permSL τ)⁻¹ * permSL (Equiv.swap i j) * permSL τ with hm
  have hact : ActsBy p m (Equiv.swap 0 1) := actsBy_conj_swap hτ0 hτ1
  have hxm : ρ' m = ρ (permSL (Equiv.swap i j)) := comp_conj_permSL_apply τ i j
  have hta : ρ (permSL (Equiv.swap i j)) * a₀ * (ρ (permSL (Equiv.swap i j)))⁻¹ = a₀⁻¹ := by
    rw [← hxm, ha₀ρ, ← map_mul, ← map_inv, ← map_mul, actsBy_swap_inv hζ hact, map_inv]
  have hmovedmem : a₀ ∈ autMovedInG A t := by
    have h1 : a₀⁻¹ ^ 2 ∈ autMovedInG A t := by
      refine ⟨⟨a₀⁻¹ ^ 2, ?_⟩, ?_, rfl⟩
      · exact A.pow_mem (A.inv_mem ha₀A) 2
      · refine Subgroup.subset_closure ⟨⟨a₀, ha₀A⟩, ?_⟩
        apply Subtype.ext
        simp only [ht, nodeOf, piAut_apply hxN, Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hta]
        group
    have h2 : a₀ = (a₀⁻¹ ^ 2) ^ ((p - 1) / 2) := by
      have hodd' : p - 1 = 2 * ((p - 1) / 2) := by
        have := hp.eq_one_or_self_of_dvd 2
        have h2p : ¬ 2 ∣ p := fun h => hp2 ((hp.eq_one_or_self_of_dvd 2 h).resolve_left (by norm_num)).symm
        omega
      have hpa : a₀ ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one a₀
      have e1 : a₀ ^ (p - 1) = a₀⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel hp.one_le, hpa]
      have e2 : a₀⁻¹ ^ (p - 1) = a₀ := by rw [inv_pow, e1, inv_inv]
      calc a₀ = a₀⁻¹ ^ (p - 1) := e2.symm
        _ = a₀⁻¹ ^ (2 * ((p - 1) / 2)) := by rw [← hodd']
        _ = (a₀⁻¹ ^ 2) ^ ((p - 1) / 2) := by rw [pow_mul]
    rw [h2]
    exact (autMovedInG A t).pow_mem h1 _
  have hzp : Subgroup.zpowers a₀ = autMovedInG A t := by
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hmovedmem) ?_
    rw [Nat.card_zpowers, hord, hmoved]
  have hgmoved : conjBy g (autMovedInG A t) = autMovedInG A t := by
    have h1 := Equivariance.autMovedInG_conj t hg
    rw [← piAut_of_mem hg, hgfix] at h1
    exact h1.symm
  have hga : g * a₀ * g⁻¹ ∈ Subgroup.zpowers a₀ := by
    rw [hzp, ← hgmoved]
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hmovedmem
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a₀ ^ n = g * a₀ * g⁻¹ :=
    (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hga)
  have hconjpow : ∀ k : ℕ, g ^ k * a₀ * (g ^ k)⁻¹ = a₀ ^ (n ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : g ^ (k + 1) * a₀ * (g ^ (k + 1))⁻¹ = g * (g ^ k * a₀ * (g ^ k)⁻¹) * g⁻¹ := by
        rw [pow_succ']
        group
      rw [e, ih, ← conj_pow, ← hn, ← pow_mul, pow_succ, mul_comm]
  have hg3a : g ^ 3 * a₀ * (g ^ 3)⁻¹ = a₀ := by
    have h1 : piAut A (g ^ 3) = 1 := by rw [piAut_pow hg, hg3]
    exact (piAut_eq_one_iff ((torusNormalizer A).pow_mem hg 3)).1 h1 a₀ ha₀A
  have hn3 : n ^ 3 % p = 1 := by
    have h1 : a₀ ^ (n ^ 3) = a₀ ^ 1 := by rw [← hconjpow 3, hg3a, pow_one]
    have h2 := (pow_eq_pow_iff_modEq).1 h1
    rw [hord] at h2
    have hp1 : 1 < p := hp.one_lt
    have : n ^ 3 % p = 1 % p := h2
    rwa [Nat.mod_eq_of_lt hp1] at this
  have hmemr : ∀ M, ∃ M', B M' = g * B M * g⁻¹ := by
    intro M
    have h1 : B M ∈ Kof A J t := by rw [hker]; exact ⟨M, rfl⟩
    have h2 : g * B M * g⁻¹ ∈ conjBy g (Kof A J t) :=
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom h1
    rw [hgK, hker] at h2
    exact h2
  choose α hα using hmemr
  have hαmul : ∀ M N, α (M * N) = α M * α N := by
    intro M N
    apply hinj
    rw [hα, map_mul, map_mul, hα, hα]
    group
  let αh : Matrix.SpecialLinearGroup (Fin 2) K →* Matrix.SpecialLinearGroup (Fin 2) K :=
    MonoidHom.mk' α hαmul
  have hαinj : Function.Injective αh := by
    intro M N h
    apply hinj
    have h1 : B (α M) = B (α N) := congrArg B h
    rw [hα, hα] at h1
    have h2 := mul_left_cancel (mul_right_cancel h1)
    exact h2
  have hαhmat : αh (hmat ζ) = hmat ζ ^ n := by
    apply hinj
    show B (α (hmat ζ)) = B (hmat ζ ^ n)
    rw [hα, map_pow, ← ha₀, hn]
  have hU : ∀ M ∈ Uplus K, αh M ∈ Uminus K := by
    intro M hM
    have hP := rootG_eq_map_Uplus (ρ := ρ) hτ0 hτ1 hij
    have hN := rootG_symm_eq_map_Uminus (ρ := ρ) hτ0 hτ1 hij
    have h1 : B M ∈ rootG ρ hij := by rw [hP]; exact ⟨M, hM, rfl⟩
    have h2 : g * B M * g⁻¹ ∈ conjBy g (rootG ρ hij) :=
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom h1
    rw [hswap, hN] at h2
    obtain ⟨M', hM', hM'e⟩ := h2
    have : α M = M' := hinj (by rw [hα]; exact hM'e.symm)
    show α M ∈ Uminus K
    rw [this]
    exact hM'
  obtain ⟨k, hk⟩ := sl2_no_swap_core ζ αh hαinj n hαhmat hU
  have hζk := zeta_pow_of_inv_pow_eq hk
  have hζk' : ζ ^ (2 * (n + 2 ^ k)) = 1 := by
    apply Units.ext
    simpa using hζk
  have hordζ : orderOf ζ = p := by
    refine orderOf_eq_prime hζ.pow ?_
    intro h1
    apply hζ.sq
    rw [h1, one_pow]
  have hdvd : p ∣ 2 * (n + 2 ^ k) := hordζ ▸ orderOf_dvd_of_pow_eq_one hζk'
  have hdvd' : p ∣ n + 2 ^ k := by
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h) hp2
    · exact h
  exact no_neg_pow_two_cube hp hp2 hL.dvd hodd hn3 (Nat.mod_eq_zero_of_dvd hdvd')

end NoSwapLine

section NoSwapGlobal

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L : Subgroup G} {f : ℕ}
  {P : Subgroup (MulAut A)} {z : MulAut A}

theorem HessSetup.fixes_roots (hS : HessSetup p A c L f P z) {g : G} (hg : g ∈ torusNormalizer A)
    (hg3 : piAut A g ^ 3 = 1) {t : MulAut A} (ht : t ∈ reflectionSet p A)
    (hfix : piAut A g * t * (piAut A g)⁻¹ = t) {S : Subgroup G} (hSr : S ∈ RootSet A f p t) :
    conjBy g S = S := by
  obtain ⟨J, hJ, K, hKf, hKfin, hKc, ρ, c', hL, htJ⟩ := hS.exists_line ht
  have ht' := ht
  obtain ⟨ht2, ht1⟩ := isAutReflection_sq ht.1
  obtain ⟨i, j, hij, rfl⟩ := hL.exists_nodeOf_eq htJ ht2 ht1
  have hkn := hS.kNode_eq hJ ht htJ
  have hset : RootSet A f p (nodeOf A ρ i j) = RootSetJ A J f (nodeOf A ρ i j) := by
    ext S
    simp only [RootSet, RootSetJ, hkn]
  have hroots := hL.rootSetJ_eq hij
  have hgK : conjBy g (Kof A J (nodeOf A ρ i j)) = Kof A J (nodeOf A ρ i j) := by
    have h1 := (hS.kNode_conj hg ht).2
    rw [hfix, hkn] at h1
    exact h1.symm
  have hnos := hL.no_swap hS.f_odd hij (hS.moved _ ht) hg hgK hfix hg3
  have hmap : ∀ S ∈ RootSet A f p (nodeOf A ρ i j), conjBy g S ∈ RootSet A f p (nodeOf A ρ i j) :=
    fun S hS' => by
      have := hS.conjBy_mem_rootSet hg ht hS'
      rwa [hfix] at this
  rw [hset, hroots] at hmap hSr
  have hne := hL.rootG_ne hij
  have hinj : Function.Injective (conjBy g : Subgroup G → Subgroup G) :=
    Subgroup.map_injective (MulAut.conj g).injective
  have hplus : conjBy g (rootG ρ hij) = rootG ρ hij := by
    rcases hmap _ (Set.mem_insert _ _) with h | h
    · exact h
    · exact absurd h hnos
  rcases hSr with rfl | hSr
  · exact hplus
  · rw [Set.mem_singleton_iff] at hSr
    subst hSr
    rcases hmap _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)) with h | h
    · exact absurd (hinj (h.trans hplus.symm)) hne.symm
    · exact h

end NoSwapGlobal

end CFSG.RankThree.PartOne.HESS
