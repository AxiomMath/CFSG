module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHDefs
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2HighestRootNormalizer

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.SeitzReduction
  CFSG.StandardType CFSG.Open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

open scoped Pointwise


private theorem rckJB123_mem_normalizer_of_conj_pinnedX
    (τ : Tag) (K : Type) [Field K] [Finite K] [CharP K 2]
    {g : ModGL τ K} (hg : g ∈ adjointGroup τ K) {c : K} (hc0 : c ≠ 0)
    (hgc : g * pinnedX τ K (highRoot τ) c * g⁻¹ ∈ rootSubgroup τ K (highRoot τ)) :
    g ∈ Subgroup.normalizer (rootSubgroup τ K (highRoot τ) : Set (ModGL τ K)) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hθ : RootCentExc.IsMaxHeight τ (highRoot τ) := isMaxHeight_highRoot τ
  have hg' : g ∈ ⋃ w, bruhatCell τ K w := by
    rw [← adjointGroup_eq_iUnion_bruhatCell]
    exact hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw
  have hB := RootCentExc.borelGroup_le_normalizer_rootSubgroup (K := K) hθ
  obtain ⟨d, hd⟩ := mem_rootSubgroup.1
    ((Subgroup.mem_normalizer_iff.1 (hB hb') _).1 (mem_rootSubgroup.2 ⟨c, rfl⟩))
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [pinnedX_zero] at hd
    have h1 : pinnedX τ K (highRoot τ) c = 1 := by
      calc pinnedX τ K (highRoot τ) c
          = b'⁻¹ * (b' * pinnedX τ K (highRoot τ) c * b'⁻¹) * b' := by group
        _ = 1 := by rw [← hd]; group
    exact hc0 (pinnedX_injective τ K (highRoot τ) (h1.trans (pinnedX_zero τ K _).symm))
  obtain ⟨c', hc'⟩ := mem_rootSubgroup.1 hgc
  obtain ⟨e, he⟩ := mem_rootSubgroup.1
    ((Subgroup.mem_normalizer_iff.1 (hB (inv_mem hb)) _).1 (mem_rootSubgroup.2 ⟨c', rfl⟩))
  have hn := RootCentExc.canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hθ.1 d
  have hkey : pinnedX τ K (w • highRoot τ) d = pinnedX τ K (highRoot τ) e := by
    rw [← hn, he, hd, hc']
    group
  have hwθ := RootCentExc.eq_of_pinnedX_eq hθ.1 (height_highRoot_pos τ) (IsRoot.smul hθ.1 w) hd0 hkey
  have hconj : ∀ a : K,
      canonicalRep (coxeterSystem τ) K w * pinnedX τ K (highRoot τ) a *
        (canonicalRep (coxeterSystem τ) K w)⁻¹ = pinnedX τ K (highRoot τ) a := by
    intro a
    rw [RootCentExc.canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hθ.1 a, hwθ]
  have hnN : canonicalRep (coxeterSystem τ) K w ∈
      Subgroup.normalizer (rootSubgroup τ K (highRoot τ) : Set (ModGL τ K)) :=
    mem_normalizer_of_forall_mul_eq fun y hy => by
      obtain ⟨a, rfl⟩ := mem_rootSubgroup.1 hy
      calc canonicalRep (coxeterSystem τ) K w * pinnedX τ K (highRoot τ) a
          = (canonicalRep (coxeterSystem τ) K w * pinnedX τ K (highRoot τ) a *
              (canonicalRep (coxeterSystem τ) K w)⁻¹) * canonicalRep (coxeterSystem τ) K w := by
            group
        _ = pinnedX τ K (highRoot τ) a * canonicalRep (coxeterSystem τ) K w := by rw [hconj a]
  exact mul_mem (mul_mem (hB hb) hnN) (hB hb')

private theorem rckJB123_parabolic_act_scalar
    (τ : Tag) (K : Type) [Field K] [Finite K] [CharP K 2]
    {g : ModGL τ K} (hg : g ∈ parabolicSubgroup τ K (Jθ τ)) :
    ∃ s : Kˣ, ∀ c : K, g * pinnedX τ K (highRoot τ) c * g⁻¹ =
      pinnedX τ K (highRoot τ) (s * c) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hθ : RootCentExc.IsMaxHeight τ (highRoot τ) := isMaxHeight_highRoot τ
  set A : Set (Fin τ.rank) := Jθ τ with hA
  have hgA : g ∈ parabolicSubgroup τ K A := by rw [hA]; exact hg
  obtain ⟨⟨q, m⟩, ⟨hq, hm, hgqm⟩, -⟩ :=
    (parabolic_root_radical_Levi_factors τ K A).2.2.2.2.2.2.1 g hgA
  dsimp only at hq hm hgqm
  subst hgqm
  have hm' : m ∈ (torusGroup τ K : Set (ModGL τ K)) *
      (Subgroup.closure (RootCentExc.leviGens τ K A) : Set (ModGL τ K)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (RootCentExc.torusGroup_le_normalizer_leviGens (τ := τ) (K := K) A)]
    exact hm
  obtain ⟨h, hh, l, hl, rfl⟩ := hm'
  obtain ⟨u, rfl⟩ := RootCentExc.torusGroup_le_range_torusHom hh
  have hqc : ∀ d : K, q * pinnedX τ K (highRoot τ) d * q⁻¹ = pinnedX τ K (highRoot τ) d := by
    intro d
    rw [(RootCentExc.commute_of_mem_posUnipotent hθ
      (parabolicRadical_le_posUnipotent A hq) d).eq, mul_inv_cancel_right]
  have hj0 : ∀ j : Fin τ.rank, j ∈ A → ∑ k, τ.cartan j k * (highRoot τ) k = 0 := by
    intro j hj
    rw [hA] at hj
    have hrefl := reflect_highRoot_of_ne τ j hj
    have h1 : (highRoot τ) j - (∑ k, τ.cartan j k * (highRoot τ) k) = (highRoot τ) j := by
      simpa only [reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one]
        using congrFun hrefl j
    linarith
  have hlevi : ∀ x ∈ RootCentExc.leviGens τ K A, ∀ d : K,
      x * pinnedX τ K (highRoot τ) d = pinnedX τ K (highRoot τ) d * x := by
    rintro x ⟨j, hj, c, rfl | rfl⟩ d
    · rw [← pinnedX_single]
      exact (RootCentExc.commute_pinnedX_of_isMaxHeight hθ (isRoot_single τ j)
        (by rw [height_single]; exact one_pos) c d).eq
    · exact RootCentExc.yUnit_mul_pinnedX_comm h2 hθ (hj0 j hj) c d
  have hlC : ∀ d : K, l * pinnedX τ K (highRoot τ) d * l⁻¹ = pinnedX τ K (highRoot τ) d := by
    intro d
    have hle : Subgroup.closure (RootCentExc.leviGens τ K A) ≤
        Subgroup.centralizer ({pinnedX τ K (highRoot τ) d} : Set (ModGL τ K)) := by
      refine (Subgroup.closure_le _).2 fun x hx => ?_
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact hlevi x hx d
    rw [Subgroup.mem_centralizer_singleton_iff.1 (hle hl), mul_inv_cancel_right]
  refine ⟨∏ i, u i ^ (∑ j, τ.cartan i j * (highRoot τ) j), fun c => ?_⟩
  calc
    (q * (RootCentExc.torusHom τ K u * l)) * pinnedX τ K (highRoot τ) c *
        (q * (RootCentExc.torusHom τ K u * l))⁻¹
        = q * (RootCentExc.torusHom τ K u * (l * pinnedX τ K (highRoot τ) c * l⁻¹) *
            (RootCentExc.torusHom τ K u)⁻¹) * q⁻¹ := by group
    _ = q * (RootCentExc.torusHom τ K u * pinnedX τ K (highRoot τ) c * (RootCentExc.torusHom τ K u)⁻¹) * q⁻¹ := by
          rw [hlC c]
    _ = q * pinnedX τ K (highRoot τ)
          ((∏ i, u i ^ (∑ j, τ.cartan i j * (highRoot τ) j)) * c) * q⁻¹ := by
          rw [RootCentExc.torusHom_conj_pinnedX (K := K) hθ.1 u c]
    _ = pinnedX τ K (highRoot τ)
          ((∏ i, u i ^ (∑ j, τ.cartan i j * (highRoot τ) j)) * c) := hqc _

theorem rckHB_mem_normalizer_of_conj
    (τ : Tag) (K : Type) [Field K] [Finite K] [CharP K 2] {i₀ : Fin τ.rank}
    (hd : RootCentExc.HighRootData τ (highRoot τ) i₀) {g : ModGL τ K} (hg : g ∈ adjointGroup τ K)
    {x : ModGL τ K} (hx : x ∈ rootSubgroup τ K (highRoot τ)) (hx1 : x ≠ 1)
    (hgx : g * x * g⁻¹ ∈ rootSubgroup τ K (highRoot τ)) :
    g ∈ Subgroup.normalizer (rootSubgroup τ K (highRoot τ) : Set (ModGL τ K)) := by
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  have hc0 : c ≠ 0 := by
    intro hc
    exact hx1 (by rw [hc, pinnedX_zero])
  exact rckJB123_mem_normalizer_of_conj_pinnedX τ K hg hc0 hgx

theorem rckHB_normalizer_act_scalar
    (τ : Tag) (K : Type) [Field K] [Finite K] [CharP K 2] {i₀ : Fin τ.rank}
    (hd : RootCentExc.HighRootData τ (highRoot τ) i₀) {g : ModGL τ K} (hg : g ∈ adjointGroup τ K)
    (hN : g ∈ Subgroup.normalizer (rootSubgroup τ K (highRoot τ) : Set (ModGL τ K))) :
    ∃ s : Kˣ, ∀ c : K, g * pinnedX τ K (highRoot τ) c * g⁻¹ = pinnedX τ K (highRoot τ) (s * c) := by
  have hP : g ∈ parabolicSubgroup τ K (Jθ τ) := by
    have h := (LieKnownR2.even_highest_root_normalizer τ K).1
    rw [← h]
    exact ⟨hN, hg⟩
  exact rckJB123_parabolic_act_scalar τ K hP

theorem rckHB_cent_highRoot
    (τ : Tag) (K : Type) [Field K] [Finite K] [CharP K 2] {i₀ : Fin τ.rank}
    (hd : RootCentExc.HighRootData τ (highRoot τ) i₀) {x : ModGL τ K}
    (hx : x ∈ rootSubgroup τ K (highRoot τ)) (hx1 : x ≠ 1) :
    adjointGroup τ K ⊓ Subgroup.centralizer {x} ≤
      Subgroup.centralizer (rootSubgroup τ K (highRoot τ) : Set (ModGL τ K)) := by
  intro k hk
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  have hc0 : c ≠ 0 := by
    intro hc
    exact hx1 (by rw [hc, pinnedX_zero])
  have hkx : k * pinnedX τ K (highRoot τ) c * k⁻¹ = pinnedX τ K (highRoot τ) c := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 hk.2, mul_inv_cancel_right]
  have hxmem : pinnedX τ K (highRoot τ) c ∈ rootSubgroup τ K (highRoot τ) :=
    mem_rootSubgroup.2 ⟨c, rfl⟩
  have hN := rckHB_mem_normalizer_of_conj τ K hd hk.1 hxmem hx1 (by rw [hkx]; exact hxmem)
  obtain ⟨s, hs⟩ := rckHB_normalizer_act_scalar τ K hd hk.1 hN
  have hsc : s * c = c := pinnedX_injective τ K (highRoot τ) (by rw [← hs c, hkx])
  have hs1 : s = 1 :=
    Units.ext (mul_right_cancel₀ hc0 (by simpa using hsc))
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hy
  have hsd : s * d = d := by rw [hs1]; simp
  have hd_eq : k * pinnedX τ K (highRoot τ) d * k⁻¹ = pinnedX τ K (highRoot τ) d := by
    rw [hs d, hsd]
  show pinnedX τ K (highRoot τ) d * k = k * pinnedX τ K (highRoot τ) d
  conv_lhs => rw [← hd_eq]
  group

theorem rckHB_TI_of_cent {M : LieUniversal} {β : Fin M.D.rank → ℤ} (hC : RCKLemmaHCent M β)
    (htr : ∀ x ∈ M.D.rootGroup β, x ≠ 1 → ∀ y ∈ M.D.rootGroup β, y ≠ 1 →
      ∃ n ∈ Subgroup.normalizer (M.D.rootGroup β : Set M.K), n * x * n⁻¹ = y) :
    RCKLemmaHTI M β := by
  intro x hx hx1 k hkx
  have hkx1 : k * x * k⁻¹ ≠ 1 := by
    intro h
    apply hx1
    calc x = k⁻¹ * (k * x * k⁻¹) * k := by group
      _ = 1 := by rw [h]; group
  obtain ⟨n, hn, hnxy⟩ := htr x hx hx1 (k * x * k⁻¹) hkx hkx1
  have hconj : (n⁻¹ * k) * x * (n⁻¹ * k)⁻¹ = x := by
    calc n⁻¹ * k * x * (n⁻¹ * k)⁻¹ = n⁻¹ * (k * x * k⁻¹) * n := by group
      _ = n⁻¹ * (n * x * n⁻¹) * n := by rw [← hnxy]
      _ = x := by group
  have hcomm : n⁻¹ * k ∈ Subgroup.centralizer ({x} : Set M.K) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (n⁻¹ * k) * x = ((n⁻¹ * k) * x * (n⁻¹ * k)⁻¹) * (n⁻¹ * k) := by group
      _ = x * (n⁻¹ * k) := by rw [hconj]
  have hNmem : n⁻¹ * k ∈ Subgroup.normalizer (M.D.rootGroup β : Set M.K) :=
    Subgroup.centralizer_le_normalizer _ (hC x hx hx1 hcomm)
  have hk_eq : n * (n⁻¹ * k) = k := by group
  rw [← hk_eq]
  exact mul_mem hn hNmem

theorem rckHB_levi_of_cent {M : LieUniversal} {β : Fin M.D.rank → ℤ} (hC : RCKLemmaHCent M β) :
    RCKLemmaHLevi M β := by
  intro x hx hx1 k hk
  exact hC x hx hx1 hk.2

end CFSG.StandardType.RCKC1
