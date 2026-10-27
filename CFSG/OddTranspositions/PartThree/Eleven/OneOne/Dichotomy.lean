module

public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Kernel
import CFSG.OddTranspositions.FusionStep
import CFSG.OddTranspositions.SixFiveInputs
import TauCeti.Algebra.Group.Subgroup.TwoTorsionClosure
import CFSG.OddTranspositions.PartThree.Eleven.OneOne.FourInvolutions
import CFSG.GroupTheory.CardSupInf
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.OddTranspositions.CommutatorSize
import CFSG.OddTranspositions.WidthOne

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

namespace ElevenOneHyp

variable {hC : HypothesisC D}

private abbrev s11y_Nu (hC : HypothesisC D) (Δ : Set G) : Subgroup G :=
  Subgroup.centralizer {hC.d} ⊓ Subgroup.normalizer Δ

private theorem s11y_frame_data (h : ElevenOneHyp hC) :
    ∃ (T : Sylow 2 (Halpha D hC.alpha)) (S : Sylow 2 G) (v : Fin 4 → G),
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ (S : Subgroup G) ∧
        ElevenFrame hC (S : Subgroup G) v := by
  let T : Sylow 2 (Halpha D hC.alpha) := Classical.arbitrary _
  obtain ⟨S, hS⟩ := Sylow.exists_comap_subtype_eq T
  have hTS : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤
      (S : Subgroup G) := by
    intro x hx
    rcases hx with ⟨t, ht, rfl⟩
    have ht' : t ∈ Subgroup.comap (Halpha D hC.alpha).subtype (S : Subgroup G) := by
      rw [hS]; exact ht
    exact Subgroup.mem_comap.mp ht'
  obtain ⟨v, hv⟩ := h.exists_frame S T hTS
  exact ⟨T, S, v, hTS, hv⟩

private theorem s11y_H_le_centralizer (h : ElevenOneHyp hC) :
    Halpha D hC.alpha ≤ Subgroup.centralizer {hC.d} := by
  rw [Halpha, Subgroup.closure_le]
  intro x hx
  change x ∈ Subgroup.centralizer {hC.d}
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact (hC.DalphaStar_subset_commute hx).2.symm.eq

private theorem s11y_centralizer_le_normalizer (h : ElevenOneHyp hC) :
    Subgroup.centralizer {hC.d} ≤ Subgroup.normalizer (Halpha D hC.alpha) := by
  refine le_trans ?_ (Subgroup.normalizer_le_normalizer_closure (DalphaStar D hC.alpha))
  intro c hc
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h.conj_mem hc hx
  · intro hx
    have hc' : c⁻¹ ∈ Subgroup.centralizer {hC.d} := (Subgroup.centralizer {hC.d}).inv_mem hc
    have h' := h.conj_mem hc' hx
    convert h' using 1
    group

private theorem s11y_T_map_eq (h : ElevenOneHyp hC) {T : Sylow 2 (Halpha D hC.alpha)}
    {S : Sylow 2 G} (hTS : (T : Subgroup (Halpha D hC.alpha)).map
      (Halpha D hC.alpha).subtype ≤ (S : Subgroup G)) :
    (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype =
      (S : Subgroup G) ⊓ Halpha D hC.alpha := by
  apply le_antisymm
  · exact le_inf hTS (Subgroup.map_subtype_le _)
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    have hP : IsPGroup 2 (Subgroup.comap (Halpha D hC.alpha).subtype (S : Subgroup G)) :=
      S.isPGroup'.comap_subtype
    have hle : (T : Subgroup (Halpha D hC.alpha)) ≤
        Subgroup.comap (Halpha D hC.alpha).subtype (S : Subgroup G) := by
      intro t ht
      exact Subgroup.mem_comap.mpr (hTS ⟨t, ht, rfl⟩)
    have heq := T.is_maximal' hP hle
    have hxT : (⟨x, hx.2⟩ : Halpha D hC.alpha) ∈ (T : Subgroup (Halpha D hC.alpha)) := by
      rw [← heq]
      exact Subgroup.mem_comap.mpr hx.1
    exact Subgroup.mem_map.mpr ⟨⟨x, hx.2⟩, hxT, rfl⟩

private theorem s11y_d_not_mem_DalphaStar (h : ElevenOneHyp hC) :
    hC.d ∉ DalphaStar D hC.alpha := by
  intro hd
  rw [hC.DalphaStar_alpha] at hd
  have hdα : hC.d ∈ hC.alpha := hC.d_mem_alpha
  rw [hC.alpha_eq_normSet_diff] at hdα
  exact hdα.2 hd

private theorem s11y_T_inter (h : ElevenOneHyp hC) {T : Sylow 2 (Halpha D hC.alpha)}
    {S : Sylow 2 G} {v : Fin 4 → G}
    (hTS : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤
      (S : Subgroup G)) (hv : ElevenFrame hC (S : Subgroup G) v) :
    ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype : Set G) ∩
      DalphaStar D hC.alpha = Set.range v := by
  rw [s11y_T_map_eq h hTS]
  ext x
  constructor
  · intro hx
    simp only [Set.mem_inter_iff, Subgroup.mem_inf] at hx
    obtain ⟨⟨hxS, hxH⟩, hxU⟩ := hx
    have hxD : x ∈ D := DalphaStar_subset hC.isBlock_alpha hxU
    have hxI : x ∈ insert hC.d (Set.range v) := by
      have hmem : x ∈ ((S : Subgroup G) : Set G) ∩ D := ⟨hxS, hxD⟩
      rwa [hv.inter_eq] at hmem
    rcases Set.mem_insert_iff.mp hxI with rfl | hxr
    · exact absurd hxU (s11y_d_not_mem_DalphaStar h)
    · exact hxr
  · intro hxr
    obtain ⟨i, hi⟩ := Set.mem_range.mp hxr
    rw [← hi]
    have hxU : v i ∈ DalphaStar D hC.alpha := hv.mem i
    have hxS : v i ∈ (S : Set G) := by
      have hmem : v i ∈ ((S : Subgroup G) : Set G) ∩ D := by
        rw [hv.inter_eq]
        exact Set.mem_insert_of_mem _ ⟨i, rfl⟩
      exact hmem.1
    exact ⟨Subgroup.mem_inf.mpr ⟨hxS, Subgroup.subset_closure hxU⟩, hxU⟩

private theorem s11y_conj_mem_range (h : ElevenOneHyp hC) {S : Subgroup G} {v : Fin 4 → G}
    (hv : ElevenFrame hC S v) {n x : G}
    (hnC : n ∈ Subgroup.centralizer {hC.d})
    (hnN : n ∈ Subgroup.normalizer ((S : Set G) ∩ D))
    (hx : x ∈ Set.range v) : n * x * n⁻¹ ∈ Set.range v := by
  have hΔ : (S : Set G) ∩ D = insert hC.d (Set.range v) := hv.inter_eq
  have hmem : x ∈ (S : Set G) ∩ D := by
    rw [hΔ]
    exact Set.mem_insert_of_mem _ hx
  have hxΔ : n * x * n⁻¹ ∈ (S : Set G) ∩ D :=
    (Subgroup.mem_set_normalizer_iff.mp hnN x).mp hmem
  rw [hΔ] at hxΔ
  rcases Set.mem_insert_iff.mp hxΔ with heq | hxr
  · exfalso
    obtain ⟨i, hi⟩ := hx
    have hnu' : hC.d * n = n * hC.d :=
      (Subgroup.mem_centralizer_iff.mp hnC) hC.d (by simp)
    have hnu : n * hC.d * n⁻¹ = hC.d := by rw [← hnu', mul_assoc, mul_inv_cancel, mul_one]
    have hnu_inv : n⁻¹ * hC.d * n = hC.d := by
      have h : n⁻¹ * (n * hC.d * n⁻¹) * n = n⁻¹ * hC.d * n :=
        congrArg (fun z => n⁻¹ * z * n) hnu
      have h2 : n⁻¹ * (n * hC.d * n⁻¹) * n = hC.d := by group
      rw [h2] at h
      exact h.symm
    have hxd : x = hC.d := by
      calc x = n⁻¹ * (n * x * n⁻¹) * n := by group
        _ = n⁻¹ * hC.d * n := by rw [heq]
        _ = hC.d := hnu_inv
    have hvi : v i = hC.d := hi.trans hxd
    exact s11y_d_not_mem_DalphaStar h (hvi ▸ hv.mem i)
  · exact hxr

private theorem s11y_sigma_exists (h : ElevenOneHyp hC) {S : Subgroup G} {v : Fin 4 → G}
    (hv : ElevenFrame hC S v)
    (n : (s11y_Nu hC ((S : Set G) ∩ D))) (i : Fin 4) :
    ∃ j, (n : G) * v i * (n : G)⁻¹ = v j := by
  obtain ⟨j, hj⟩ := s11y_conj_mem_range h hv n.2.1 n.2.2 ⟨i, rfl⟩
  exact ⟨j, hj.symm⟩

private noncomputable def s11y_sigmaFun (h : ElevenOneHyp hC) {S : Subgroup G} {v : Fin 4 → G}
    (hv : ElevenFrame hC S v)
    (n : (s11y_Nu hC ((S : Set G) ∩ D))) (i : Fin 4) :
    Fin 4 := Classical.choose (s11y_sigma_exists h hv n i)

private theorem s11y_sigmaFun_spec (h : ElevenOneHyp hC) {S : Subgroup G} {v : Fin 4 → G}
    (hv : ElevenFrame hC S v)
    (n : (s11y_Nu hC ((S : Set G) ∩ D))) (i : Fin 4) :
    (n : G) * v i * (n : G)⁻¹ = v (s11y_sigmaFun h hv n i) :=
  Classical.choose_spec (s11y_sigma_exists h hv n i)

private theorem s11y_sigmaFun_injective (h : ElevenOneHyp hC) {S : Subgroup G}
    {v : Fin 4 → G} (hv : ElevenFrame hC S v)
    (n : (s11y_Nu hC ((S : Set G) ∩ D))) :
    Function.Injective (s11y_sigmaFun h hv n) := by
  intro i j hij
  apply hv.injective
  have h1 : (n : G) * v i * (n : G)⁻¹ = (n : G) * v j * (n : G)⁻¹ := by
    rw [s11y_sigmaFun_spec h hv n i, s11y_sigmaFun_spec h hv n j, hij]
  have h2 : v i = v j := by
    have := congrArg (fun z => (n : G)⁻¹ * z * (n : G)) h1
    simpa using this
  exact h2

private theorem s11y_sigmaFun_bijective (h : ElevenOneHyp hC) {S : Subgroup G}
    {v : Fin 4 → G} (hv : ElevenFrame hC S v)
    (n : (s11y_Nu hC ((S : Set G) ∩ D))) :
    Function.Bijective (s11y_sigmaFun h hv n) :=
  ⟨s11y_sigmaFun_injective h hv n,
    Finite.surjective_of_injective (s11y_sigmaFun_injective h hv n)⟩

private noncomputable def s11y_sigmaEquiv (h : ElevenOneHyp hC) {S : Subgroup G}
    {v : Fin 4 → G} (hv : ElevenFrame hC S v)
    (n : (s11y_Nu hC ((S : Set G) ∩ D))) :
    Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (s11y_sigmaFun h hv n) (s11y_sigmaFun_bijective h hv n)

private theorem s11y_sigmaEquiv_apply (h : ElevenOneHyp hC) {S : Subgroup G} {v : Fin 4 → G}
    (hv : ElevenFrame hC S v)
    (n : (s11y_Nu hC ((S : Set G) ∩ D))) (i : Fin 4) :
    (s11y_sigmaEquiv h hv n) i = s11y_sigmaFun h hv n i :=
  Equiv.ofBijective_apply _ _ _

private theorem s11y_sigmaEquiv_spec (h : ElevenOneHyp hC) {S : Subgroup G} {v : Fin 4 → G}
    (hv : ElevenFrame hC S v)
    (n : (s11y_Nu hC ((S : Set G) ∩ D))) (i : Fin 4) :
    (n : G) * v i * (n : G)⁻¹ = v ((s11y_sigmaEquiv h hv n) i) := by
  rw [s11y_sigmaEquiv_apply]
  exact s11y_sigmaFun_spec h hv n i

private noncomputable def s11y_sigma (h : ElevenOneHyp hC) {S : Subgroup G} {v : Fin 4 → G}
    (hv : ElevenFrame hC S v) :
    (s11y_Nu hC ((S : Set G) ∩ D)) →*
      Equiv.Perm (Fin 4) :=
  MonoidHom.mk' (s11y_sigmaEquiv h hv) (fun n m => by
    apply Equiv.Perm.ext
    intro i
    rw [Equiv.Perm.mul_apply]
    have hm : (m : G) * v i * (m : G)⁻¹ = v ((s11y_sigmaEquiv h hv m) i) :=
      s11y_sigmaEquiv_spec h hv m i
    have hn : (n : G) * v ((s11y_sigmaEquiv h hv m) i) * (n : G)⁻¹ =
        v ((s11y_sigmaEquiv h hv n) ((s11y_sigmaEquiv h hv m) i)) :=
      s11y_sigmaEquiv_spec h hv n _
    have h3 : ((n * m : s11y_Nu hC ((S : Set G) ∩ D)) : G) * v i *
          (((n * m : s11y_Nu hC ((S : Set G) ∩ D)) : G))⁻¹ =
        (n : G) * ((m : G) * v i * (m : G)⁻¹) * (n : G)⁻¹ := by
      simp only [Subgroup.coe_mul]
      group
    have key : v ((s11y_sigmaEquiv h hv (n * m)) i) =
        v ((s11y_sigmaEquiv h hv n) ((s11y_sigmaEquiv h hv m) i)) := by
      rw [← s11y_sigmaEquiv_spec h hv (n * m) i, h3, hm, hn]
    exact hv.injective key)

private theorem s11y_sigma_apply (h : ElevenOneHyp hC) {S : Subgroup G} {v : Fin 4 → G}
    (hv : ElevenFrame hC S v) (n : s11y_Nu hC ((S : Set G) ∩ D)) (i : Fin 4) :
    (s11y_sigma h hv n) i = (s11y_sigmaEquiv h hv n) i :=
  rfl

private theorem s11y_closure_le_H (h : ElevenOneHyp hC) {S : Subgroup G} {v : Fin 4 → G}
    (hv : ElevenFrame hC S v) :
    Subgroup.closure ((S : Set G) ∩ D) ≤ Halpha D hC.alpha := by
  rw [Subgroup.closure_le]
  rw [hv.inter_eq]
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hxr
  · exact h.d_mem_Halpha
  · obtain ⟨i, rfl⟩ := hxr
    exact Subgroup.subset_closure (hv.mem i)

private theorem s11y_range_mem_S (h : ElevenOneHyp hC) {S : Subgroup G} {v : Fin 4 → G}
    (hv : ElevenFrame hC S v) (i : Fin 4) : v i ∈ (S : Set G) := by
  have : v i ∈ (S : Set G) ∩ D := by
    rw [hv.inter_eq]
    exact Set.mem_insert_of_mem _ ⟨i, rfl⟩
  exact this.1

private theorem s11y_pairwise_commute (h : ElevenOneHyp hC) {S : Subgroup G} {v : Fin 4 → G}
    (hv : ElevenFrame hC S v) (hS2 : IsPGroup 2 S) :
    ((insert hC.d (Set.range v) : Set G)).Pairwise (fun a b => Commute a b) := by
  intro a ha b hb hab
  rw [Set.mem_insert_iff] at ha hb
  rcases ha with rfl | ⟨i, rfl⟩ <;> rcases hb with rfl | ⟨j, rfl⟩
  · exact absurd rfl hab
  · exact (hC.DalphaStar_subset_commute (hv.mem j)).2.symm
  · exact (hC.DalphaStar_subset_commute (hv.mem i)).2
  · have hij : i ≠ j := fun hij => hab (by rw [hij])
    exact CFSG.OddTranspositions.commute_of_mul_mem_of_isPGroup hC.setup.oddT hS2
      (DalphaStar_subset hC.isBlock_alpha (hv.mem i))
      (DalphaStar_subset hC.isBlock_alpha (hv.mem j))
      (S.mul_mem (s11y_range_mem_S h hv i) (s11y_range_mem_S h hv j))

private theorem s11y_isMulCommutative_closure (h : ElevenOneHyp hC) {S : Subgroup G}
    {v : Fin 4 → G} (hv : ElevenFrame hC S v) (hS2 : IsPGroup 2 S) :
    IsMulCommutative (Subgroup.closure ((S : Set G) ∩ D)) := by
  rw [hv.inter_eq]
  exact Subgroup.isMulCommutative_closure (s11y_pairwise_commute h hv hS2)

private theorem s11y_sigma_eq_one_iff (h : ElevenOneHyp hC) {S : Subgroup G} {v : Fin 4 → G}
    (hv : ElevenFrame hC S v) (hS2 : IsPGroup 2 S) (n : s11y_Nu hC ((S : Set G) ∩ D)) :
    s11y_sigma h hv n = 1 ↔ (n : G) ∈ Subgroup.closure ((S : Set G) ∩ D) := by
  constructor
  · intro h1
    rw [← h.centralizer_frame hv]
    change (n : G) ∈ Subgroup.centralizer ((S : Set G) ∩ D)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : x ∈ insert hC.d (Set.range v) := by rwa [hv.inter_eq] at hx
    rcases Set.mem_insert_iff.mp hx' with rfl | hxr
    · exact (Subgroup.mem_centralizer_iff.mp n.2.1) hC.d (by simp)
    · obtain ⟨i, rfl⟩ := hxr
      have hσi : (s11y_sigmaEquiv h hv n) i = i := by
        have := congrArg (fun τ : Equiv.Perm (Fin 4) => τ i) h1
        simpa only [s11y_sigma_apply, Equiv.Perm.one_apply] using this
      have hspec := s11y_sigmaEquiv_spec h hv n i
      rw [hσi] at hspec
      calc v i * (n : G) = (n : G) * v i * (n : G)⁻¹ * (n : G) := by rw [hspec]
        _ = (n : G) * v i := by group
  · intro h1
    haveI := s11y_isMulCommutative_closure h hv hS2
    apply Equiv.Perm.ext
    intro i
    have hviB : v i ∈ Subgroup.closure ((S : Set G) ∩ D) := by
      rw [hv.inter_eq]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
    have hcomm : Commute (n : G) (v i) := by
      have h := IsMulCommutative.is_comm.comm
        (⟨(n : G), h1⟩ : Subgroup.closure ((S : Set G) ∩ D))
        (⟨v i, hviB⟩ : Subgroup.closure ((S : Set G) ∩ D))
      show (n : G) * v i = v i * (n : G)
      exact congrArg Subtype.val h
    have hfix : (n : G) * v i * (n : G)⁻¹ = v i := by
      rw [hcomm.eq]; group
    have key : v ((s11y_sigma h hv n) i) = v i := by
      have h1 : (s11y_sigma h hv n) i = (s11y_sigmaEquiv h hv n) i := s11y_sigma_apply h hv n i
      rw [h1, ← s11y_sigmaEquiv_spec h hv n i]
      exact hfix
    exact hv.injective key

private theorem s11y_mem_Nu_of_perm (h : ElevenOneHyp hC) {S : Subgroup G} {v : Fin 4 → G}
    (hv : ElevenFrame hC S v) {g : G} (hg : g ∈ Halpha D hC.alpha)
    {τ : Equiv.Perm (Fin 4)} (hτ : ∀ i, g * v i * g⁻¹ = v (τ i)) :
    g ∈ s11y_Nu hC ((S : Set G) ∩ D) := by
  have hgC : g ∈ Subgroup.centralizer {hC.d} := s11y_H_le_centralizer h hg
  refine Subgroup.mem_inf.mpr ⟨hgC, ?_⟩
  have h' : hC.d * g = g * hC.d := (Subgroup.mem_centralizer_iff.mp hgC) hC.d (by simp)
  have hgu : g * hC.d * g⁻¹ = hC.d := by
    calc g * hC.d * g⁻¹ = g * hC.d * g⁻¹ := rfl
      _ = hC.d * g * g⁻¹ := by rw [← h']
      _ = hC.d := by group
  have hgu_inv : g⁻¹ * hC.d * g = hC.d := by
    calc g⁻¹ * hC.d * g = g⁻¹ * (hC.d * g) := by group
      _ = g⁻¹ * (g * hC.d) := by rw [h']
      _ = hC.d := by group
  have hgτinv : ∀ j, g⁻¹ * v j * g = v (τ.symm j) := by
    intro j
    have hj := hτ (τ.symm j)
    rw [Equiv.apply_symm_apply] at hj
    calc g⁻¹ * v j * g = g⁻¹ * (g * v (τ.symm j) * g⁻¹) * g := by rw [hj]
      _ = v (τ.symm j) := by group
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx' : x ∈ insert hC.d (Set.range v) := by rwa [hv.inter_eq] at hx
    rcases Set.mem_insert_iff.mp hx' with rfl | hxr
    · rw [hgu, hv.inter_eq]
      exact Set.mem_insert_iff.mpr (Or.inl rfl)
    · obtain ⟨i, rfl⟩ := hxr
      rw [hτ i, hv.inter_eq]
      exact Set.mem_insert_iff.mpr (Or.inr ⟨τ i, rfl⟩)
  · intro hx
    have hx' : g * x * g⁻¹ ∈ insert hC.d (Set.range v) := by rwa [hv.inter_eq] at hx
    rcases Set.mem_insert_iff.mp hx' with hgu' | hxr
    · have hx_eq : x = hC.d := by
        calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
          _ = g⁻¹ * hC.d * g := by rw [hgu']
          _ = hC.d := hgu_inv
      rw [hx_eq, hv.inter_eq]
      exact Set.mem_insert_iff.mpr (Or.inl rfl)
    · obtain ⟨j, hj⟩ := hxr
      have hx_eq : x = v (τ.symm j) := by
        calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
          _ = g⁻¹ * v j * g := by rw [hj]
          _ = v (τ.symm j) := hgτinv j
      rw [hx_eq, hv.inter_eq]
      exact Set.mem_insert_iff.mpr (Or.inr ⟨τ.symm j, rfl⟩)

private theorem s11y_sigma_eq_of_perm (h : ElevenOneHyp hC) {S : Subgroup G} {v : Fin 4 → G}
    (hv : ElevenFrame hC S v) {g : G} (hg : g ∈ s11y_Nu hC ((S : Set G) ∩ D))
    {τ : Equiv.Perm (Fin 4)} (hτ : ∀ i, g * v i * g⁻¹ = v (τ i)) :
    s11y_sigma h hv ⟨g, hg⟩ = τ := by
  apply Equiv.Perm.ext
  intro i
  have key : v ((s11y_sigma h hv ⟨g, hg⟩) i) = v (τ i) := by
    have h1 : (s11y_sigma h hv ⟨g, hg⟩) i = (s11y_sigmaEquiv h hv ⟨g, hg⟩) i :=
      s11y_sigma_apply h hv ⟨g, hg⟩ i
    rw [h1, ← s11y_sigmaEquiv_spec h hv ⟨g, hg⟩ i]
    exact hτ i
  exact hv.injective key

private theorem s11y_alternating_le_range (h : ElevenOneHyp hC) {S : Subgroup G} {v : Fin 4 → G}
    (hv : ElevenFrame hC S v) :
    alternatingGroup (Fin 4) ≤ (s11y_sigma h hv).range := by
  intro τ hτ
  obtain ⟨g, hg, hgτ⟩ := hv.alternating τ hτ
  have hgNu : g ∈ s11y_Nu hC ((S : Set G) ∩ D) := s11y_mem_Nu_of_perm h hv hg hgτ
  exact MonoidHom.mem_range.mpr ⟨⟨g, hgNu⟩, s11y_sigma_eq_of_perm h hv hgNu hgτ⟩

private theorem s11y_sigma_mem_alt_iff (h : ElevenOneHyp hC) {S : Subgroup G} {v : Fin 4 → G}
    (hv : ElevenFrame hC S v) (hS2 : IsPGroup 2 S)
    (n : s11y_Nu hC ((S : Set G) ∩ D)) :
    s11y_sigma h hv n ∈ alternatingGroup (Fin 4) ↔
      (n : G) ∈ Halpha D hC.alpha := by
  constructor
  · intro hmem
    obtain ⟨g, hg, hgτ⟩ := hv.alternating (s11y_sigma h hv n) hmem
    have hgNu : g ∈ s11y_Nu hC ((S : Set G) ∩ D) := s11y_mem_Nu_of_perm h hv hg hgτ
    have hσg : s11y_sigma h hv ⟨g, hgNu⟩ = s11y_sigma h hv n :=
      s11y_sigma_eq_of_perm h hv hgNu hgτ
    have hprodNu : (n : G) * g⁻¹ ∈ s11y_Nu hC ((S : Set G) ∩ D) :=
      (s11y_Nu hC _).mul_mem n.2 ((s11y_Nu hC _).inv_mem hgNu)
    have hprod_eq : (⟨(n : G) * g⁻¹, hprodNu⟩ : s11y_Nu hC ((S : Set G) ∩ D)) =
        n * ⟨g, hgNu⟩⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hσprod : s11y_sigma h hv ⟨(n : G) * g⁻¹, hprodNu⟩ = 1 := by
      rw [hprod_eq, map_mul, ← hσg]
      simp
    have h1 : (n : G) * g⁻¹ ∈ Subgroup.closure ((S : Set G) ∩ D) :=
      (s11y_sigma_eq_one_iff h hv hS2 _).mp hσprod
    have : (n : G) = ((n : G) * g⁻¹) * g := by group
    rw [this]
    exact (Halpha D hC.alpha).mul_mem (s11y_closure_le_H h hv h1) hg
  · intro hnH
    exact hv.even (n : G) hnH (s11y_sigma h hv n) (fun i => by
      rw [s11y_sigma_apply]
      exact s11y_sigmaEquiv_spec h hv n i)

private theorem s11y_mem_normalizer_map {C : Subgroup G} {Q : Subgroup C} {a : C}
    (ha : a ∈ Subgroup.normalizer Q) :
    (a : G) ∈ Subgroup.normalizer (Q.map (Subgroup.subtype C)) := by
  rw [Subgroup.mem_normalizer_iff_conj_image_eq] at ha ⊢
  have h := congrArg (fun S : Set C => (Subgroup.subtype C : C → G) '' S) ha
  rw [Set.image_image] at h
  have h2 : (fun q : C => (Subgroup.subtype C) ((MulAut.conj a) q)) =
      (fun q : C => (MulAut.conj (a : G)) ((Subgroup.subtype C) q)) := by
    funext q; rfl
  rw [h2] at h
  have h3 : (Subgroup.subtype C : C → G) '' (Q : Set C) =
      (Q.map (Subgroup.subtype C) : Set G) := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact Subgroup.mem_map.mpr ⟨q, hq, rfl⟩
    · intro hx
      change x ∈ (Q.map (Subgroup.subtype C) : Subgroup G) at hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      exact ⟨q, hq, rfl⟩
  rw [← Set.image_image, h3] at h
  exact h

private theorem s11y_conj_mem_Delta (h : ElevenOneHyp hC) {S : Sylow 2 G} {v : Fin 4 → G}
    {T : Sylow 2 (Halpha D hC.alpha)} (hv : ElevenFrame hC (S : Subgroup G) v)
    (hTS : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ S)
    {n : G} (hnC : n ∈ Subgroup.centralizer {hC.d})
    (hnT : n ∈ Subgroup.normalizer
      ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype)) :
    ∀ x ∈ (S : Set G) ∩ D, n * x * n⁻¹ ∈ (S : Set G) ∩ D := by
  intro x hx
  have hTset : (((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype : Subgroup G) :
      Set G) ∩ DalphaStar D hC.alpha = Set.range v := s11y_T_inter h hTS hv
  have hnu : n * hC.d * n⁻¹ = hC.d := by
    have h' : hC.d * n = n * hC.d := (Subgroup.mem_centralizer_iff.mp hnC) hC.d (by simp)
    calc n * hC.d * n⁻¹ = hC.d * n * n⁻¹ := by rw [← h']
      _ = hC.d := by group
  have hnD : ∀ y ∈ DalphaStar D hC.alpha, n * y * n⁻¹ ∈ DalphaStar D hC.alpha :=
    fun y hy => h.conj_mem hnC hy
  have hnT' : ∀ y ∈ (((T : Subgroup (Halpha D hC.alpha)).map
      (Halpha D hC.alpha).subtype : Subgroup G) : Set G), n * y * n⁻¹ ∈
      (((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype : Subgroup G) : Set G) :=
    fun y hy => (Subgroup.mem_set_normalizer_iff.mp hnT y).mp hy
  have hx' : x ∈ insert hC.d (Set.range v) := by
    have hx'' : x ∈ ((S : Subgroup G) : Set G) ∩ D := hx
    rwa [hv.inter_eq] at hx''
  change n * x * n⁻¹ ∈ ((S : Subgroup G) : Set G) ∩ D
  rw [hv.inter_eq]
  rcases Set.mem_insert_iff.mp hx' with rfl | hxr
  · rw [hnu]
    exact Set.mem_insert_iff.mpr (Or.inl rfl)
  · obtain ⟨i, rfl⟩ := hxr
    have hviT : v i ∈ (((T : Subgroup (Halpha D hC.alpha)).map
        (Halpha D hC.alpha).subtype : Subgroup G) : Set G) ∩ DalphaStar D hC.alpha := by
      rw [hTset]
      exact ⟨i, rfl⟩
    have hconj : n * v i * n⁻¹ ∈ (((T : Subgroup (Halpha D hC.alpha)).map
        (Halpha D hC.alpha).subtype : Subgroup G) : Set G) ∩ DalphaStar D hC.alpha :=
      ⟨hnT' (v i) hviT.1, hnD (v i) hviT.2⟩
    rw [hTset] at hconj
    exact Set.mem_insert_iff.mpr (Or.inr hconj)

private theorem s11y_mem_Nu_of_normalizes_T (h : ElevenOneHyp hC) {S : Sylow 2 G} {v : Fin 4 → G}
    {T : Sylow 2 (Halpha D hC.alpha)} (hv : ElevenFrame hC (S : Subgroup G) v)
    (hTS : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ S)
    {n : G} (hnC : n ∈ Subgroup.centralizer {hC.d})
    (hnT : n ∈ Subgroup.normalizer
      ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype)) :
    n ∈ s11y_Nu hC ((S : Set G) ∩ D) := by
  refine Subgroup.mem_inf.mpr ⟨hnC, ?_⟩
  rw [Subgroup.mem_set_normalizer_iff]
  intro x
  constructor
  · exact s11y_conj_mem_Delta h hv hTS hnC hnT x
  · intro hx
    have hnC' : n⁻¹ ∈ Subgroup.centralizer {hC.d} := (Subgroup.centralizer {hC.d}).inv_mem hnC
    have hnT' : n⁻¹ ∈ Subgroup.normalizer
        ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) :=
      (Subgroup.normalizer _).inv_mem hnT
    have := s11y_conj_mem_Delta h hv hTS hnC' hnT' (n * x * n⁻¹) hx
    convert this using 1
    group

private theorem s11y_frattini (h : ElevenOneHyp hC) {S : Sylow 2 G} {v : Fin 4 → G}
    {T : Sylow 2 (Halpha D hC.alpha)} (hv : ElevenFrame hC (S : Subgroup G) v)
    (hTS : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ S) :
    Subgroup.centralizer {hC.d} ≤ Halpha D hC.alpha ⊔ s11y_Nu hC ((S : Set G) ∩ D) := by
  intro c hc
  let C : Subgroup G := Subgroup.centralizer {hC.d}
  let H : Subgroup G := Halpha D hC.alpha
  have hHC : H ≤ C := s11y_H_le_centralizer h
  let N : Subgroup C := H.subgroupOf C
  haveI : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer (s11y_centralizer_le_normalizer h)
  let e : H ≃* N := (Subgroup.subgroupOfEquivOfLe hHC).symm
  let P : Sylow 2 N := Sylow.mapSurjective (f := e.toMonoidHom) (EquivLike.surjective e) T
  have hsup : Subgroup.normalizer (P.map N.subtype) ⊔ N = ⊤ := Sylow.normalizer_sup_eq_top P
  have hcN : (⟨c, hc⟩ : C) ∈ Subgroup.normalizer (P.map N.subtype) ⊔ N := by
    rw [hsup]; exact Subgroup.mem_top _
  obtain ⟨a, ha, b, hb, hab⟩ := (Subgroup.mem_sup_of_normal_right.mp hcN)
  have hbH : (b : G) ∈ H := hb
  have hPcoe : (P : Subgroup N) = (T : Subgroup H).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (EquivLike.surjective e) T
  have hcomp : ((Subgroup.subtype C).comp N.subtype).comp e.toMonoidHom = H.subtype := by
    ext x; rfl
  have hPmap : (P.map N.subtype).map (Subgroup.subtype C) =
      (T : Subgroup H).map H.subtype := by
    calc (P.map N.subtype).map (Subgroup.subtype C)
        = P.map ((Subgroup.subtype C).comp N.subtype) := by rw [Subgroup.map_map]
      _ = ((T : Subgroup H).map e.toMonoidHom).map
            ((Subgroup.subtype C).comp N.subtype) := by rw [hPcoe]
      _ = (T : Subgroup H).map
            (((Subgroup.subtype C).comp N.subtype).comp e.toMonoidHom) := by
            rw [Subgroup.map_map]
      _ = (T : Subgroup H).map H.subtype := by rw [hcomp]
  have haT : (a : G) ∈ Subgroup.normalizer
      ((T : Subgroup H).map H.subtype) := by
    have := s11y_mem_normalizer_map ha
    rwa [hPmap] at this
  have haNu : (a : G) ∈ s11y_Nu hC ((S : Set G) ∩ D) :=
    s11y_mem_Nu_of_normalizes_T h hv hTS a.2 haT
  have hcab : (a : G) * (b : G) = c := by
    have := congrArg (Subgroup.subtype C) hab
    simpa using this
  rw [← hcab, sup_comm]
  exact Subgroup.mul_mem_sup haNu hbH

private theorem s11y_sup_eq_centralizer (h : ElevenOneHyp hC) {S : Sylow 2 G} {v : Fin 4 → G}
    {T : Sylow 2 (Halpha D hC.alpha)} (hv : ElevenFrame hC (S : Subgroup G) v)
    (hTS : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ S) :
    Halpha D hC.alpha ⊔ s11y_Nu hC ((S : Set G) ∩ D) = Subgroup.centralizer {hC.d} :=
  le_antisymm (sup_le (s11y_H_le_centralizer h) inf_le_left) (s11y_frattini h hv hTS)

private theorem s11y_relIndex_eq (h : ElevenOneHyp hC) {S : Sylow 2 G} {v : Fin 4 → G}
    {T : Sylow 2 (Halpha D hC.alpha)} (hv : ElevenFrame hC (S : Subgroup G) v)
    (hTS : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ S) :
    (Halpha D hC.alpha).relIndex (Subgroup.centralizer {hC.d}) =
      (Halpha D hC.alpha).relIndex (s11y_Nu hC ((S : Set G) ∩ D)) := by
  let C : Subgroup G := Subgroup.centralizer {hC.d}
  let H : Subgroup G := Halpha D hC.alpha
  let Nu : Subgroup G := s11y_Nu hC ((S : Set G) ∩ D)
  have hHC : H ≤ C := s11y_H_le_centralizer h
  have hNuC : Nu ≤ C := inf_le_left
  have hsup : H ⊔ Nu = C := s11y_sup_eq_centralizer h hv hTS
  haveI : (H.subgroupOf C).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (s11y_centralizer_le_normalizer h)
  have hmap : (Nu.subgroupOf C ⊔ H.subgroupOf C).map (Subgroup.subtype C) = C := by
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hNuC, inf_of_le_left hHC, sup_comm, hsup]
  have hsupC : Nu.subgroupOf C ⊔ H.subgroupOf C = ⊤ := by
    apply Subgroup.ext
    intro x
    constructor
    · intro _; trivial
    · intro _
      have hx : (x : G) ∈ (Nu.subgroupOf C ⊔ H.subgroupOf C).map (Subgroup.subtype C) := by
        rw [hmap]; exact x.2
      rw [Subgroup.mem_map] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have hyx' : y = x := Subtype.ext hyx
      rwa [← hyx']
  calc H.relIndex C = (H.subgroupOf C).index := rfl
    _ = (H.subgroupOf C).relIndex ⊤ := (Subgroup.relIndex_top_right (H.subgroupOf C)).symm
    _ = (H.subgroupOf C).relIndex (Nu.subgroupOf C ⊔ H.subgroupOf C) := by rw [hsupC]
    _ = (H.subgroupOf C).relIndex (Nu.subgroupOf C) :=
        Subgroup.relIndex_sup_right (Nu.subgroupOf C) (H.subgroupOf C)
    _ = H.relIndex Nu := Subgroup.relIndex_subgroupOf hNuC

private theorem s11y_index_dvd_two (h : ElevenOneHyp hC) {S : Sylow 2 G} {v : Fin 4 → G}
    {T : Sylow 2 (Halpha D hC.alpha)} (hv : ElevenFrame hC (S : Subgroup G) v)
    (hTS : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ S)
    (hS2 : IsPGroup 2 (S : Subgroup G)) :
    (Halpha D hC.alpha).relIndex (Subgroup.centralizer {hC.d}) ∣ 2 := by
  let H : Subgroup G := Halpha D hC.alpha
  let Nu : Subgroup G := s11y_Nu hC ((S : Set G) ∩ D)
  rw [s11y_relIndex_eq h hv hTS]
  have hker : H.subgroupOf Nu = (alternatingGroup (Fin 4)).comap (s11y_sigma h hv) := by
    ext n
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    exact (s11y_sigma_mem_alt_iff h hv hS2 n).symm
  show (H.subgroupOf Nu).index ∣ 2
  rw [hker]
  have h1 : ((alternatingGroup (Fin 4)).comap (s11y_sigma h hv)).index =
      (alternatingGroup (Fin 4)).relIndex (s11y_sigma h hv).range :=
    Subgroup.index_comap (alternatingGroup (Fin 4)) (s11y_sigma h hv)
  rw [h1]
  have hdvd := Subgroup.relIndex_dvd_index_of_le (s11y_alternating_le_range h hv :
    alternatingGroup (Fin 4) ≤ (s11y_sigma h hv).range)
  rwa [alternatingGroup.index_eq_two] at hdvd

private theorem s11y_sigma_surjective (h : ElevenOneHyp hC) {S : Sylow 2 G} {v : Fin 4 → G}
    (hv : ElevenFrame hC (S : Subgroup G) v) (hS2 : IsPGroup 2 (S : Subgroup G))
    (x : s11y_Nu hC ((S : Set G) ∩ D))
    (hx : s11y_sigma h hv x ∉ alternatingGroup (Fin 4)) :
    (s11y_sigma h hv).range = ⊤ := by
  apply top_le_iff.mp
  intro τ _
  by_cases hτ : τ ∈ alternatingGroup (Fin 4)
  · exact s11y_alternating_le_range h hv hτ
  · have h2 : τ * (s11y_sigma h hv x)⁻¹ ∈ alternatingGroup (Fin 4) := by
      rw [Subgroup.mul_mem_iff_of_index_two (alternatingGroup.index_eq_two (α := Fin 4))]
      exact ⟨fun hτ' => absurd hτ' hτ,
        fun hx' => absurd ((alternatingGroup (Fin 4)).inv_mem_iff.mp hx') hx⟩
    obtain ⟨m, hm⟩ := s11y_alternating_le_range h hv h2
    refine ⟨m * x, ?_⟩
    rw [map_mul, hm]
    group

private theorem s11y_exists_y (h : ElevenOneHyp hC) {S : Sylow 2 G} {v : Fin 4 → G}
    (hv : ElevenFrame hC (S : Subgroup G) v) (hS2 : IsPGroup 2 (S : Subgroup G))
    (x : s11y_Nu hC ((S : Set G) ∩ D))
    (hx : s11y_sigma h hv x ∉ alternatingGroup (Fin 4))
    (n₀ : G) (hn₀ : n₀ ∈ Subgroup.normalizer ((S : Set G) ∩ D))
    (hn₀u : n₀ * hC.d * n₀⁻¹ = v 2) :
    ∃ y ∈ Subgroup.normalizer ((S : Set G) ∩ D),
      y * hC.d * y⁻¹ = v 2 ∧ y * v 0 * y⁻¹ = v 0 ∧ y * v 1 * y⁻¹ = v 1 ∧
        y * v 2 * y⁻¹ = v 3 ∧ y * v 3 * y⁻¹ = hC.d := by
  classical
  have hdn : hC.d ∉ Set.range v := fun ⟨i, hi⟩ => s11y_d_not_mem_DalphaStar h (hi ▸ hv.mem i)
  let w : Fin 4 → G := fun i =>
    if i = 0 then v 0 else if i = 1 then v 1 else if i = 2 then v 3 else hC.d
  have hw0 : w 0 = v 0 := by simp [w]
  have hw1 : w 1 = v 1 := by simp [w]
  have hw2 : w 2 = v 3 := by simp [w]
  have hw3 : w 3 = hC.d := by simp [w]
  have hdn' : ∀ i, v i ≠ hC.d := fun i hi => hdn ⟨i, hi⟩
  have hw_inj : Function.Injective w := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [hw0, hw1, hw2, hw3, hv.injective.eq_iff, hdn']
  have hn₀inv : n₀⁻¹ ∈ Subgroup.normalizer ((S : Set G) ∩ D) :=
    (Subgroup.normalizer _).inv_mem hn₀
  have hΔ : (S : Set G) ∩ D = insert hC.d (Set.range v) := hv.inter_eq
  have hwmem : ∀ i, w i ∈ (S : Set G) ∩ D := by
    intro i
    rw [hΔ]
    fin_cases i <;>
      simp only [hw0, hw1, hw2, hw3, Set.mem_insert_iff, Set.mem_range]
    · exact Or.inr ⟨0, rfl⟩
    · exact Or.inr ⟨1, rfl⟩
    · exact Or.inr ⟨3, rfl⟩
    · exact Or.inl rfl
  have hwv2 : ∀ i, w i ≠ v 2 := by
    intro i
    fin_cases i <;> simp only [hw0, hw1, hw2, hw3]
    · exact fun hw => by exact absurd (hv.injective hw) (by decide)
    · exact fun hw => by exact absurd (hv.injective hw) (by decide)
    · exact fun hw => by exact absurd (hv.injective hw) (by decide)
    · intro hw
      have hdu : hC.d = v 2 := hw3 ▸ hw
      exact absurd (hdu.symm ▸ hv.mem 2) (s11y_d_not_mem_DalphaStar h)
  have hconj_mem : ∀ i, n₀⁻¹ * w i * n₀ ∈ Set.range v := by
    intro i
    have hmem : n₀⁻¹ * w i * n₀ ∈ insert hC.d (Set.range v) := by
      rw [← hΔ]
      simpa using (Subgroup.mem_set_normalizer_iff.mp hn₀inv (w i)).mp (hwmem i)
    rw [Set.mem_insert_iff] at hmem
    rcases hmem with hmem | hmem
    · exfalso
      apply hwv2 i
      have hthis : n₀ * (n₀⁻¹ * w i * n₀) * n₀⁻¹ = n₀ * hC.d * n₀⁻¹ := by rw [hmem]
      rw [hn₀u] at hthis
      have hwi : w i = v 2 := by rw [← hthis]; group
      exact hwi
    · exact hmem
  let e : Fin 4 ≃ ↥(Set.range v) := Equiv.ofInjective v hv.injective
  let φ : Fin 4 → ↥(Set.range v) := fun i => ⟨n₀⁻¹ * w i * n₀, hconj_mem i⟩
  have hφ_inj : Function.Injective φ := by
    intro i j hij
    apply hw_inj
    have h1 : n₀⁻¹ * w i * n₀ = n₀⁻¹ * w j * n₀ := Subtype.ext_iff.mp hij
    have := congrArg (fun z => n₀ * z * n₀⁻¹) h1
    simpa using this
  have hφ_surj : Function.Surjective φ :=
    (Finite.injective_iff_surjective_of_equiv e).mp hφ_inj
  have hφ_bij : Function.Bijective φ := ⟨hφ_inj, hφ_surj⟩
  let τ : Equiv.Perm (Fin 4) := (Equiv.ofBijective φ hφ_bij).trans e.symm
  have hτ_spec : ∀ i, n₀⁻¹ * w i * n₀ = v (τ i) := by
    intro i
    have h1 : e (τ i) = φ i := Equiv.apply_symm_apply e (φ i)
    have h2 : v (τ i) = n₀⁻¹ * w i * n₀ := by
      have := congrArg Subtype.val h1
      simpa [e, φ] using this
    exact h2.symm
  have hsur := s11y_sigma_surjective h hv hS2 x hx
  have hmem : τ ∈ (s11y_sigma h hv).range := by rw [hsur]; exact Subgroup.mem_top _
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp hmem
  refine ⟨n₀ * m, (Subgroup.normalizer _).mul_mem hn₀ m.2.2, ?_, ?_, ?_, ?_, ?_⟩
  · calc n₀ * m * hC.d * (n₀ * m)⁻¹ = n₀ * ((m : G) * hC.d * (m : G)⁻¹) * n₀⁻¹ := by
          group
      _ = n₀ * hC.d * n₀⁻¹ := by
            rw [← (Subgroup.mem_centralizer_iff.mp m.2.1) hC.d (by simp)]
            group
      _ = v 2 := hn₀u
  · have h1 : (m : G) * v 0 * (m : G)⁻¹ = v (τ 0) := by
      rw [s11y_sigmaEquiv_spec h hv m 0, ← s11y_sigma_apply, hm]
    calc n₀ * m * v 0 * (n₀ * m)⁻¹ = n₀ * ((m : G) * v 0 * (m : G)⁻¹) * n₀⁻¹ := by
          group
      _ = n₀ * v (τ 0) * n₀⁻¹ := by rw [h1]
      _ = n₀ * (n₀⁻¹ * w 0 * n₀) * n₀⁻¹ := by rw [← hτ_spec 0]
      _ = v 0 := by rw [hw0]; group
  · have h1 : (m : G) * v 1 * (m : G)⁻¹ = v (τ 1) := by
      rw [s11y_sigmaEquiv_spec h hv m 1, ← s11y_sigma_apply, hm]
    calc n₀ * m * v 1 * (n₀ * m)⁻¹ = n₀ * ((m : G) * v 1 * (m : G)⁻¹) * n₀⁻¹ := by
          group
      _ = n₀ * v (τ 1) * n₀⁻¹ := by rw [h1]
      _ = n₀ * (n₀⁻¹ * w 1 * n₀) * n₀⁻¹ := by rw [← hτ_spec 1]
      _ = v 1 := by rw [hw1]; group
  · have h1 : (m : G) * v 2 * (m : G)⁻¹ = v (τ 2) := by
      rw [s11y_sigmaEquiv_spec h hv m 2, ← s11y_sigma_apply, hm]
    calc n₀ * m * v 2 * (n₀ * m)⁻¹ = n₀ * ((m : G) * v 2 * (m : G)⁻¹) * n₀⁻¹ := by
          group
      _ = n₀ * v (τ 2) * n₀⁻¹ := by rw [h1]
      _ = n₀ * (n₀⁻¹ * w 2 * n₀) * n₀⁻¹ := by rw [← hτ_spec 2]
      _ = v 3 := by rw [hw2]; group
  · have h1 : (m : G) * v 3 * (m : G)⁻¹ = v (τ 3) := by
      rw [s11y_sigmaEquiv_spec h hv m 3, ← s11y_sigma_apply, hm]
    calc n₀ * m * v 3 * (n₀ * m)⁻¹ = n₀ * ((m : G) * v 3 * (m : G)⁻¹) * n₀⁻¹ := by
          group
      _ = n₀ * v (τ 3) * n₀⁻¹ := by rw [h1]
      _ = n₀ * (n₀⁻¹ * w 3 * n₀) * n₀⁻¹ := by rw [← hτ_spec 3]
      _ = hC.d := by rw [hw3]; group

private theorem s11y_card_closure_le_comm {X : Type*} [CommGroup X] {ι : Type*}
    (s : Finset ι) (f : ι → X) (hsq : ∀ i ∈ s, f i ^ 2 = 1) :
    Nat.card (Subgroup.closure (f '' (↑s : Set ι))) ≤ 2 ^ s.card := by
  have hset := TauCeti.closure_image_eq_image_powerset s f hsq
  have hmain : ((fun S : Finset ι => ∏ i ∈ S, f i) '' (↑s.powerset : Set (Finset ι))).ncard
      ≤ 2 ^ s.card := by
    calc ((fun S : Finset ι => ∏ i ∈ S, f i) '' (↑s.powerset : Set (Finset ι))).ncard
        ≤ ((↑s.powerset : Set (Finset ι))).ncard := Set.ncard_image_le s.powerset.finite_toSet
      _ = 2 ^ s.card := by rw [Set.ncard_coe_finset, Finset.card_powerset]
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset]
  exact hmain

private theorem s11y_v_mem_D {S : Subgroup G} {v : Fin 4 → G}
    (hv : ElevenFrame hC S v) (i : Fin 4) : v i ∈ D :=
  DalphaStar_subset hC.isBlock_alpha (hv.mem i)

private theorem s11y_v_sq {S : Subgroup G} {v : Fin 4 → G}
    (hv : ElevenFrame hC S v) (i : Fin 4) : v i * v i = 1 := by
  have h2 : orderOf (v i) = 2 := hC.setup.oddT.1 (v i) (s11y_v_mem_D hv i)
  have hpow : v i ^ 2 = 1 := by
    have := pow_orderOf_eq_one (v i)
    rwa [h2] at this
  simpa [pow_two] using hpow

private theorem s11y_v_commute (h : ElevenOneHyp hC) {S : Subgroup G} {v : Fin 4 → G}
    (hv : ElevenFrame hC S v) (hS2 : IsPGroup 2 S) (i j : Fin 4) : Commute (v i) (v j) := by
  rcases eq_or_ne i j with rfl | hij
  · exact Commute.refl _
  · exact s11y_pairwise_commute h hv hS2
      (Set.mem_insert_of_mem _ ⟨i, rfl⟩) (Set.mem_insert_of_mem _ ⟨j, rfl⟩)
      (fun h => hij (hv.injective h))

private theorem s11y_closure_inter_eq {S : Subgroup G} {v : Fin 4 → G}
    (hv : ElevenFrame hC S v) :
    Subgroup.closure ((S : Set G) ∩ D) = Subgroup.closure (Set.range v) := by
  rw [hv.inter_eq]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | ⟨i, rfl⟩)
    · rw [← hv.prod_eq]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.subset_closure ⟨0, rfl⟩) (Subgroup.subset_closure ⟨1, rfl⟩))
        (Subgroup.subset_closure ⟨2, rfl⟩)) (Subgroup.subset_closure ⟨3, rfl⟩)
    · exact Subgroup.subset_closure ⟨i, rfl⟩
  · rw [Subgroup.closure_le]
    rintro x ⟨i, rfl⟩
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨i, rfl⟩)

private theorem s11y_card_closure_range (h : ElevenOneHyp hC) {S : Sylow 2 G} {v : Fin 4 → G}
    (hv : ElevenFrame hC (S : Subgroup G) v) :
    Nat.card (Subgroup.closure (Set.range v)) = 16 := by
  classical
  have hcommB : (Set.range v).Pairwise (fun a b => Commute a b) := by
    rintro a ⟨i, rfl⟩ b ⟨j, rfl⟩ _
    exact s11y_v_commute h hv S.isPGroup' i j
  have hsq : ∀ i, v i * v i = 1 := s11y_v_sq hv
  have hupper : Nat.card (Subgroup.closure (Set.range v)) ≤ 16 := by
    let B : Subgroup G := Subgroup.closure (Set.range v)
    letI : CommGroup B := Subgroup.closureCommGroupOfComm hcommB
    let f : Fin 4 → B := fun i => ⟨v i, Subgroup.subset_closure ⟨i, rfl⟩⟩
    have hf_sq : ∀ i ∈ (Finset.univ : Finset (Fin 4)), f i ^ 2 = 1 := by
      intro i _
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]
      change v i * v i = (1 : G)
      exact hsq i
    have hle := s11y_card_closure_le_comm (Finset.univ : Finset (Fin 4)) f hf_sq
    have hrange : (f '' (↑(Finset.univ : Finset (Fin 4)) : Set (Fin 4))) = Set.range f := by
      rw [Finset.coe_univ, Set.image_univ]
    rw [hrange] at hle
    norm_num at hle
    have hmap_le : (Subgroup.closure (Set.range f)).map (Subgroup.subtype B) ≤ B :=
      Subgroup.map_subtype_le _
    have hB_le : B ≤ (Subgroup.closure (Set.range f)).map (Subgroup.subtype B) := by
      rw [Subgroup.closure_le]
      rintro x ⟨i, rfl⟩
      exact Subgroup.mem_map.mpr ⟨f i, Subgroup.subset_closure ⟨i, rfl⟩, rfl⟩
    have hmap_eq : (Subgroup.closure (Set.range f)).map (Subgroup.subtype B) = B :=
      le_antisymm hmap_le hB_le
    have hcard : Nat.card B = Nat.card (Subgroup.closure (Set.range f)) := by
      have h1 : Nat.card B = Nat.card ((Subgroup.closure (Set.range f)).map
          (Subgroup.subtype B)) :=
        (congrArg (fun H : Subgroup G => Nat.card H) hmap_eq).symm
      rw [h1]
      exact Subgroup.card_map_of_injective (Subgroup.subtype_injective B)
    change Nat.card B ≤ 16
    rw [hcard]
    exact hle
  have hC8 : Nat.card (Subgroup.closure (Set.range v \ {v 0})) = 8 := hv.card_closure 0
  have hle : Subgroup.closure (Set.range v \ {v 0}) ≤ Subgroup.closure (Set.range v) :=
    Subgroup.closure_mono Set.sdiff_subset
  have hdvd : 8 ∣ Nat.card (Subgroup.closure (Set.range v)) := by
    rw [← hC8]
    exact Subgroup.card_dvd_of_le hle
  have hne8 : Nat.card (Subgroup.closure (Set.range v)) ≠ 8 := by
    intro h8
    have heq : Subgroup.closure (Set.range v \ {v 0}) = Subgroup.closure (Set.range v) :=
      Subgroup.eq_of_le_of_card_ge hle (by simp [h8, hC8])
    have hgen : ∀ i : Fin 4, i ≠ 0 →
        v i ∈ Subgroup.closure (Set.range v \ {v 0}) := by
      intro i hi
      exact Subgroup.subset_closure ⟨⟨i, rfl⟩, fun h =>
        hi (hv.injective (Set.mem_singleton_iff.mp h))⟩
    have hv0C : v 0 ∈ Subgroup.closure (Set.range v \ {v 0}) := by
      rw [heq]
      exact Subgroup.subset_closure ⟨0, rfl⟩
    have hd : hC.d ∈ Subgroup.closure (Set.range v \ {v 0}) := by
      rw [← hv.prod_eq]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hv0C
        (hgen 1 (by decide))) (hgen 2 (by decide))) (hgen 3 (by decide))
    exact hv.d_not_mem 0 hd
  have hpos : 0 < Nat.card (Subgroup.closure (Set.range v)) := Nat.card_pos
  obtain ⟨k, hk⟩ := hdvd
  have hk2 : k = 2 := by
    have hklt : k ≤ 2 := by
      rw [hk] at hupper
      omega
    have hkne : k ≠ 1 := by
      rintro rfl
      rw [mul_one] at hk
      exact hne8 hk
    have hkne0 : k ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hk
      omega
    omega
  rw [hk, hk2]

private theorem s11y_x₁_data (h : ElevenOneHyp hC) {S : Sylow 2 G} {v : Fin 4 → G}
    (hv : ElevenFrame hC (S : Subgroup G) v) (hS2 : IsPGroup 2 (S : Subgroup G))
    (x : s11y_Nu hC ((S : Set G) ∩ D))
    (hx : s11y_sigma h hv x ∉ alternatingGroup (Fin 4)) :
    ∃ x₁ : s11y_Nu hC ((S : Set G) ∩ D),
      s11y_sigma h hv x₁ = Equiv.swap 0 1 ∧
        (x₁ : G) * v 0 * (x₁ : G)⁻¹ = v 1 ∧
        (x₁ : G) * v 1 * (x₁ : G)⁻¹ = v 0 ∧
        (x₁ : G) * v 2 * (x₁ : G)⁻¹ = v 2 ∧
        (x₁ : G) * v 3 * (x₁ : G)⁻¹ = v 3 := by
  have hsur := s11y_sigma_surjective h hv hS2 x hx
  obtain ⟨x₁, hx₁σ⟩ : ∃ x₁ : s11y_Nu hC ((S : Set G) ∩ D),
      s11y_sigma h hv x₁ = Equiv.swap 0 1 := by
    have hmem : Equiv.swap (0 : Fin 4) 1 ∈ (s11y_sigma h hv).range := by
      rw [hsur]
      exact Subgroup.mem_top _
    exact MonoidHom.mem_range.mp hmem
  have hspec : ∀ i, (x₁ : G) * v i * (x₁ : G)⁻¹ = v ((Equiv.swap 0 1) i) := by
    intro i
    have h' := s11y_sigmaEquiv_spec h hv x₁ i
    rwa [← s11y_sigma_apply h hv x₁ i, hx₁σ] at h'
  refine ⟨x₁, hx₁σ, ?_, ?_, ?_, ?_⟩
  · have h' := hspec 0
    rwa [Equiv.swap_apply_left] at h'
  · have h' := hspec 1
    rwa [Equiv.swap_apply_right] at h'
  · have h' := hspec 2
    rw [Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 4) ≠ 0)
      (by decide : (2 : Fin 4) ≠ 1)] at h'
    exact h'
  · have h' := hspec 3
    rw [Equiv.swap_apply_of_ne_of_ne (by decide : (3 : Fin 4) ≠ 0)
      (by decide : (3 : Fin 4) ≠ 1)] at h'
    exact h'

private theorem s11y_exists_n₀_y (h : ElevenOneHyp hC) {S : Sylow 2 G} {v : Fin 4 → G}
    (hv : ElevenFrame hC (S : Subgroup G) v) (hS2 : IsPGroup 2 (S : Subgroup G))
    (x : s11y_Nu hC ((S : Set G) ∩ D))
    (hx : s11y_sigma h hv x ∉ alternatingGroup (Fin 4)) :
    ∃ y ∈ Subgroup.normalizer ((S : Set G) ∩ D),
      y * hC.d * y⁻¹ = v 2 ∧ y * v 0 * y⁻¹ = v 0 ∧ y * v 1 * y⁻¹ = v 1 ∧
        y * v 2 * y⁻¹ = v 3 ∧ y * v 3 * y⁻¹ = hC.d := by
  have hdΔ : hC.d ∈ (S : Set G) ∩ D := by
    rw [show (S : Set G) ∩ D = insert hC.d (Set.range v) from hv.inter_eq]
    exact Set.mem_insert_iff.mpr (Or.inl rfl)
  have hv2Δ : v 2 ∈ (S : Set G) ∩ D := by
    rw [show (S : Set G) ∩ D = insert hC.d (Set.range v) from hv.inter_eq]
    exact Set.mem_insert_iff.mpr (Or.inr ⟨2, rfl⟩)
  obtain ⟨n₀, hn₀, hn₀u⟩ := CFSG.OddTranspositions.sylow_inter_D_transitive
    hC.setup.isClass hC.setup.oddT S hdΔ hv2Δ
  exact s11y_exists_y h hv hS2 x hx n₀ hn₀ hn₀u

private theorem s11y_beta_mem_closure (h : ElevenOneHyp hC) {S : Sylow 2 G} {v : Fin 4 → G}
    (hv : ElevenFrame hC (S : Subgroup G) v) (hS2 : IsPGroup 2 (S : Subgroup G))
    (x₁ : s11y_Nu hC ((S : Set G) ∩ D))
    (hx0 : (x₁ : G) * v 0 * (x₁ : G)⁻¹ = v 1)
    (hx1 : (x₁ : G) * v 1 * (x₁ : G)⁻¹ = v 0)
    (hx2 : (x₁ : G) * v 2 * (x₁ : G)⁻¹ = v 2)
    (hx3 : (x₁ : G) * v 3 * (x₁ : G)⁻¹ = v 3)
    {y : G} (hyN : y ∈ Subgroup.normalizer ((S : Set G) ∩ D))
    (hyu : y * hC.d * y⁻¹ = v 2)
    (hy0 : y * v 0 * y⁻¹ = v 0) (hy1 : y * v 1 * y⁻¹ = v 1)
    (hy2 : y * v 2 * y⁻¹ = v 3) (hy3 : y * v 3 * y⁻¹ = hC.d) :
    (x₁ : G)⁻¹ * (y * (x₁ : G) * y⁻¹) ∈ Subgroup.closure (Set.range v) := by
  classical
  have hx₁d : (x₁ : G) * hC.d * (x₁ : G)⁻¹ = hC.d := by
    have hc := (Subgroup.mem_centralizer_iff.mp x₁.2.1) hC.d (by simp)
    calc (x₁ : G) * hC.d * (x₁ : G)⁻¹ = hC.d * (x₁ : G) * (x₁ : G)⁻¹ := by rw [← hc]
      _ = hC.d := by group
  have hyinv0 : y⁻¹ * v 0 * y = v 0 := by
    have h' : v 0 = y⁻¹ * v 0 * y := by
      calc v 0 = y⁻¹ * (y * v 0 * y⁻¹) * y := by group
        _ = y⁻¹ * v 0 * y := by rw [hy0]
    exact h'.symm
  have hyinv1 : y⁻¹ * v 1 * y = v 1 := by
    have h' : v 1 = y⁻¹ * v 1 * y := by
      calc v 1 = y⁻¹ * (y * v 1 * y⁻¹) * y := by group
        _ = y⁻¹ * v 1 * y := by rw [hy1]
    exact h'.symm
  have hyinv2 : y⁻¹ * v 2 * y = hC.d := by
    have h' : hC.d = y⁻¹ * v 2 * y := by
      calc hC.d = y⁻¹ * (y * hC.d * y⁻¹) * y := by group
        _ = y⁻¹ * v 2 * y := by rw [hyu]
    exact h'.symm
  have hyinv3 : y⁻¹ * v 3 * y = v 2 := by
    have h' : v 2 = y⁻¹ * v 3 * y := by
      calc v 2 = y⁻¹ * (y * v 2 * y⁻¹) * y := by group
        _ = y⁻¹ * v 3 * y := by rw [hy2]
    exact h'.symm
  have hyinvD : y⁻¹ * hC.d * y = v 3 := by
    have h' : v 3 = y⁻¹ * hC.d * y := by
      calc v 3 = y⁻¹ * (y * v 3 * y⁻¹) * y := by group
        _ = y⁻¹ * hC.d * y := by rw [hy3]
    exact h'.symm
  have hconjD : (y * (x₁ : G) * y⁻¹) * hC.d * (y * (x₁ : G) * y⁻¹)⁻¹ = hC.d := by
    calc (y * (x₁ : G) * y⁻¹) * hC.d * (y * (x₁ : G) * y⁻¹)⁻¹
        = y * ((x₁ : G) * (y⁻¹ * hC.d * y) * (x₁ : G)⁻¹) * y⁻¹ := by group
      _ = y * ((x₁ : G) * v 3 * (x₁ : G)⁻¹) * y⁻¹ := by rw [hyinvD]
      _ = y * v 3 * y⁻¹ := by rw [hx3]
      _ = hC.d := hy3
  have hx₂_v : ∀ i, (y * (x₁ : G) * y⁻¹) * v i * (y * (x₁ : G) * y⁻¹)⁻¹ =
      (x₁ : G) * v i * (x₁ : G)⁻¹ := by
    intro i
    fin_cases i
    · calc (y * (x₁ : G) * y⁻¹) * v 0 * (y * (x₁ : G) * y⁻¹)⁻¹
          = y * ((x₁ : G) * (y⁻¹ * v 0 * y) * (x₁ : G)⁻¹) * y⁻¹ := by group
        _ = y * ((x₁ : G) * v 0 * (x₁ : G)⁻¹) * y⁻¹ := by rw [hyinv0]
        _ = y * v 1 * y⁻¹ := by rw [hx0]
        _ = v 1 := hy1
        _ = (x₁ : G) * v 0 * (x₁ : G)⁻¹ := hx0.symm
    · calc (y * (x₁ : G) * y⁻¹) * v 1 * (y * (x₁ : G) * y⁻¹)⁻¹
          = y * ((x₁ : G) * (y⁻¹ * v 1 * y) * (x₁ : G)⁻¹) * y⁻¹ := by group
        _ = y * ((x₁ : G) * v 1 * (x₁ : G)⁻¹) * y⁻¹ := by rw [hyinv1]
        _ = y * v 0 * y⁻¹ := by rw [hx1]
        _ = v 0 := hy0
        _ = (x₁ : G) * v 1 * (x₁ : G)⁻¹ := hx1.symm
    · calc (y * (x₁ : G) * y⁻¹) * v 2 * (y * (x₁ : G) * y⁻¹)⁻¹
          = y * ((x₁ : G) * (y⁻¹ * v 2 * y) * (x₁ : G)⁻¹) * y⁻¹ := by group
        _ = y * ((x₁ : G) * hC.d * (x₁ : G)⁻¹) * y⁻¹ := by rw [hyinv2]
        _ = y * hC.d * y⁻¹ := by rw [hx₁d]
        _ = v 2 := hyu
        _ = (x₁ : G) * v 2 * (x₁ : G)⁻¹ := hx2.symm
    · calc (y * (x₁ : G) * y⁻¹) * v 3 * (y * (x₁ : G) * y⁻¹)⁻¹
          = y * ((x₁ : G) * (y⁻¹ * v 3 * y) * (x₁ : G)⁻¹) * y⁻¹ := by group
        _ = y * ((x₁ : G) * v 2 * (x₁ : G)⁻¹) * y⁻¹ := by rw [hyinv3]
        _ = y * v 2 * y⁻¹ := by rw [hx2]
        _ = v 3 := hy2
        _ = (x₁ : G) * v 3 * (x₁ : G)⁻¹ := hx3.symm
  have hx₂Nu : y * (x₁ : G) * y⁻¹ ∈ s11y_Nu hC ((S : Set G) ∩ D) := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      have hthis : (y * (x₁ : G) * y⁻¹) * hC.d = hC.d * (y * (x₁ : G) * y⁻¹) := by
        calc (y * (x₁ : G) * y⁻¹) * hC.d
            = ((y * (x₁ : G) * y⁻¹) * hC.d * (y * (x₁ : G) * y⁻¹)⁻¹) *
                (y * (x₁ : G) * y⁻¹) := by group
          _ = hC.d * (y * (x₁ : G) * y⁻¹) := by rw [hconjD]
      exact hthis.symm
    · exact (Subgroup.normalizer _).mul_mem
        ((Subgroup.normalizer _).mul_mem hyN x₁.2.2)
        ((Subgroup.normalizer _).inv_mem hyN)
  have hx₁spec : ∀ i, (x₁ : G) * v i * (x₁ : G)⁻¹ = v ((s11y_sigma h hv x₁) i) := by
    intro i
    rw [s11y_sigma_apply h hv x₁ i]
    exact s11y_sigmaEquiv_spec h hv x₁ i
  have hσx₂ : s11y_sigma h hv ⟨y * (x₁ : G) * y⁻¹, hx₂Nu⟩ = s11y_sigma h hv x₁ :=
    s11y_sigma_eq_of_perm h hv hx₂Nu (fun i => (hx₂_v i).trans (hx₁spec i))
  have hzNu : (x₁ : G)⁻¹ * (y * (x₁ : G) * y⁻¹) ∈ s11y_Nu hC ((S : Set G) ∩ D) :=
    (s11y_Nu hC _).mul_mem ((s11y_Nu hC _).inv_mem x₁.2) hx₂Nu
  have hzeq : (⟨(x₁ : G)⁻¹ * (y * (x₁ : G) * y⁻¹), hzNu⟩ :
        s11y_Nu hC ((S : Set G) ∩ D)) = x₁⁻¹ * ⟨y * (x₁ : G) * y⁻¹, hx₂Nu⟩ := by
    apply Subtype.ext
    rfl
  have hσz : s11y_sigma h hv ⟨(x₁ : G)⁻¹ * (y * (x₁ : G) * y⁻¹), hzNu⟩ = 1 := by
    rw [hzeq, map_mul, map_inv, hσx₂]
    simp
  have hbΔ : ((⟨(x₁ : G)⁻¹ * (y * (x₁ : G) * y⁻¹), hzNu⟩ :
      s11y_Nu hC ((S : Set G) ∩ D)) : G) ∈ Subgroup.closure ((S : Set G) ∩ D) :=
    (s11y_sigma_eq_one_iff h hv hS2 ⟨_, hzNu⟩).mp hσz
  rw [show Subgroup.closure ((S : Set G) ∩ D) = Subgroup.closure (Set.range v) from
    s11y_closure_inter_eq hv] at hbΔ
  exact hbΔ

private theorem s11y_not_mem_H_of_sigma_swap (h : ElevenOneHyp hC) {S : Sylow 2 G}
    {v : Fin 4 → G} (hv : ElevenFrame hC (S : Subgroup G) v)
    (hS2 : IsPGroup 2 (S : Subgroup G)) {t : G}
    (htNu : t ∈ s11y_Nu hC ((S : Set G) ∩ D))
    (htσ : s11y_sigma h hv ⟨t, htNu⟩ = Equiv.swap 0 1) :
    t ∉ Halpha D hC.alpha := by
  intro htH
  have hmem : s11y_sigma h hv ⟨t, htNu⟩ ∈ alternatingGroup (Fin 4) :=
    (s11y_sigma_mem_alt_iff h hv hS2 ⟨t, htNu⟩).mpr htH
  rw [htσ, Equiv.Perm.mem_alternatingGroup,
    Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 1)] at hmem
  exact absurd hmem (by decide)

private theorem s11y_ne_one_of_sigma_swap (h : ElevenOneHyp hC) {S : Sylow 2 G}
    {v : Fin 4 → G} (hv : ElevenFrame hC (S : Subgroup G) v) {t : G}
    (htNu : t ∈ s11y_Nu hC ((S : Set G) ∩ D))
    (htσ : s11y_sigma h hv ⟨t, htNu⟩ = Equiv.swap 0 1) : t ≠ 1 := by
  intro h1
  have hsub : (⟨t, htNu⟩ : s11y_Nu hC ((S : Set G) ∩ D)) = 1 := by
    apply Subtype.ext
    simp [h1]
  rw [hsub, map_one] at htσ
  exact absurd htσ.symm (by
    intro hswap
    have h0 := congrArg (fun e : Equiv.Perm (Fin 4) => e 0) hswap
    simp only [Equiv.swap_apply_left, Equiv.Perm.one_apply] at h0
    exact absurd h0 (by decide))

private theorem s11y_exists_involution (h : ElevenOneHyp hC) {S : Sylow 2 G} {v : Fin 4 → G}
    {T : Sylow 2 (Halpha D hC.alpha)} (hv : ElevenFrame hC (S : Subgroup G) v)
    (hTS : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ S)
    (hS2 : IsPGroup 2 (S : Subgroup G))
    (x : s11y_Nu hC ((S : Set G) ∩ D))
    (hx : s11y_sigma h hv x ∉ alternatingGroup (Fin 4)) :
    ∃ y ∈ Subgroup.centralizer {hC.d}, y ∉ Halpha D hC.alpha ∧ orderOf y = 2 := by
  classical
  obtain ⟨x₁, hx₁σ, hx0, hx1, hx2, hx3⟩ := s11y_x₁_data h hv hS2 x hx
  obtain ⟨y, hyN, hyu, hy0, hy1, hy2, hy3⟩ := s11y_exists_n₀_y h hv hS2 x hx
  have hq : (x₁ : G) * (x₁ : G) ∈ Subgroup.closure (Set.range v) := by
    have h1 : s11y_sigma h hv (x₁ * x₁) = 1 := by
      rw [map_mul, hx₁σ]
      apply Equiv.ext
      intro i
      simp [Equiv.swap_apply_self]
    have h2 : ((x₁ * x₁ : s11y_Nu hC ((S : Set G) ∩ D)) : G) ∈
        Subgroup.closure ((S : Set G) ∩ D) :=
      (s11y_sigma_eq_one_iff h hv hS2 (x₁ * x₁)).mp h1
    rw [show Subgroup.closure ((S : Set G) ∩ D) = Subgroup.closure (Set.range v) from
      s11y_closure_inter_eq hv] at h2
    simpa using h2
  have hb : (x₁ : G)⁻¹ * (y * (x₁ : G) * y⁻¹) ∈
      Subgroup.closure (Set.range v) :=
    s11y_beta_mem_closure h hv hS2 x₁ hx0 hx1 hx2 hx3 hyN hyu hy0 hy1 hy2 hy3
  have hcase := mul_self_eq_one_or_of_four_involutions (v := v) (x := (x₁ : G)) (y := y)
    (s11y_v_commute h hv hS2) (s11y_v_sq hv) (s11y_card_closure_range h hv)
    hx0 hx1 hx2 hx3 hy0 hy1 hy2 (hy3.trans hv.prod_eq.symm) hq hb
  have hv0Nu : v 0 ∈ s11y_Nu hC ((S : Set G) ∩ D) :=
    s11y_mem_Nu_of_perm h hv (Subgroup.subset_closure (hv.mem 0)) (τ := 1) (fun i => by
      rw [(s11y_v_commute h hv hS2 0 i).eq, Equiv.Perm.one_apply]
      group)
  have hσv0 : s11y_sigma h hv ⟨v 0, hv0Nu⟩ = 1 :=
    s11y_sigma_eq_of_perm h hv hv0Nu (τ := 1) (fun i => by
      rw [(s11y_v_commute h hv hS2 0 i).eq, Equiv.Perm.one_apply]
      group)
  rcases hcase with hcase | hcase
  · refine ⟨(x₁ : G), x₁.2.1, ?_, ?_⟩
    · exact s11y_not_mem_H_of_sigma_swap h hv hS2 x₁.2 hx₁σ
    · exact orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hcase)
        (s11y_ne_one_of_sigma_swap h hv x₁.2 hx₁σ)
  · have htNu : (x₁ : G) * v 0 ∈ s11y_Nu hC ((S : Set G) ∩ D) :=
      (s11y_Nu hC _).mul_mem x₁.2 hv0Nu
    have htσ : s11y_sigma h hv ⟨(x₁ : G) * v 0, htNu⟩ = Equiv.swap 0 1 := by
      have heq : (⟨(x₁ : G) * v 0, htNu⟩ : s11y_Nu hC ((S : Set G) ∩ D)) =
          x₁ * ⟨v 0, hv0Nu⟩ := by
        apply Subtype.ext
        rfl
      rw [heq, map_mul, hx₁σ, hσv0, mul_one]
    refine ⟨(x₁ : G) * v 0, (Subgroup.centralizer {hC.d}).mul_mem x₁.2.1 hv0Nu.1,
      s11y_not_mem_H_of_sigma_swap h hv hS2 htNu htσ, ?_⟩
    have ht2 : ((x₁ : G) * v 0) * ((x₁ : G) * v 0) = 1 := by
      have hxv : (x₁ : G) * v 0 = v 1 * (x₁ : G) := by
        rw [← hx0]
        group
      calc ((x₁ : G) * v 0) * ((x₁ : G) * v 0)
          = (((x₁ : G) * v 0) * (x₁ : G)) * v 0 := by group
        _ = ((v 1 * (x₁ : G)) * (x₁ : G)) * v 0 := by rw [hxv]
        _ = v 1 * ((x₁ : G) * (x₁ : G)) * v 0 := by group
        _ = v 1 * (v 0 * v 1) * v 0 := by rw [hcase]
        _ = v 1 * v 1 * v 0 * v 0 := by
              rw [← (s11y_v_commute h hv hS2 1 0).eq]
              group
        _ = 1 := by simp [s11y_v_sq hv 1, s11y_v_sq hv 0]
    exact orderOf_eq_prime (p := 2) (by rw [pow_two]; exact ht2)
      (s11y_ne_one_of_sigma_swap h hv htNu htσ)

end ElevenOneHyp

theorem ElevenOneHyp.centralizer_le_or_index_two {hC : HypothesisC D} (h : ElevenOneHyp hC) :
    Subgroup.centralizer {hC.d} ≤ Halpha D hC.alpha ∨
      ((Halpha D hC.alpha).relIndex (Subgroup.centralizer {hC.d}) = 2 ∧
        ∃ x ∈ Subgroup.centralizer {hC.d}, x ∉ Halpha D hC.alpha ∧ orderOf x = 2) := by
  classical
  obtain ⟨T, S, v, hTS, hv⟩ := s11y_frame_data h
  have hS2 : IsPGroup 2 (S : Subgroup G) := S.isPGroup'
  by_cases hodd : ∃ x : s11y_Nu hC ((S : Set G) ∩ D),
      s11y_sigma h hv x ∉ alternatingGroup (Fin 4)
  · right
    obtain ⟨x, hx⟩ := hodd
    refine ⟨?_, s11y_exists_involution h hv hTS hS2 x hx⟩
    have hdvd := s11y_index_dvd_two h hv hTS hS2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exfalso
      have hCH : Subgroup.centralizer {hC.d} ≤ Halpha D hC.alpha :=
        Subgroup.relIndex_eq_one.mp h1
      have hxC : (x : G) ∈ Subgroup.centralizer {hC.d} :=
        (inf_le_left : s11y_Nu hC ((S : Set G) ∩ D) ≤ Subgroup.centralizer {hC.d}) x.2
      exact hx ((s11y_sigma_mem_alt_iff h hv hS2 x).mpr (hCH hxC))
    · exact h2
  · left
    have hNuH : s11y_Nu hC ((S : Set G) ∩ D) ≤ Halpha D hC.alpha := by
      intro n hn
      by_contra hc
      exact hodd ⟨⟨n, hn⟩, fun hmem =>
        hc ((s11y_sigma_mem_alt_iff h hv hS2 ⟨n, hn⟩).mp hmem)⟩
    rw [← s11y_sup_eq_centralizer h hv hTS]
    exact sup_le le_rfl hNuH

end CFSG.OddTranspositions.PartThree
