module

public import CFSG.RankThree.SteinbergR3ECALinearPrimaryBlocks
public import CFSG.RankThree.PartOne.KC.PlaneLifting

public section

namespace CFSG.RankThree.CALinearPrimary

open Polynomial Module CFSG CFSG.RankThree.LocalRank CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary

variable {n : ℕ} {K : Type*} [Field K]

theorem eq_one_of_mem_scalars [Finite K] {p : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ Nat.card K - 1)
    (hn : 0 < n) {z : Matrix.SpecialLinearGroup (Fin n) K} (hz : z ∈ scalars n K)
    (hzp : z ^ p = 1) : z = 1 := by
  obtain ⟨c, -, hc⟩ := mem_scalars.1 hz
  have hcp : c ^ p = 1 := by
    have h3 := Matrix.SpecialLinearGroup.coe_pow z p
    rw [hzp, Matrix.SpecialLinearGroup.coe_one, hc, Matrix.scalar_apply, Matrix.diagonal_pow] at h3
    have h4 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M ⟨0, hn⟩ ⟨0, hn⟩) h3
    simp only [Matrix.one_apply_eq, Matrix.diagonal_apply_eq, Pi.pow_apply] at h4
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, ← h4, Units.val_one])
  have hord : orderOf c = 1 := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hcp) with h | h
    · exact h
    · have h2 := orderOf_dvd_natCard c
      rw [h, Nat.card_units] at h2
      exact absurd h2 hpq
  have hc1 : c = 1 := orderOf_eq_one_iff.mp hord
  apply Subtype.ext
  rw [hc, hc1, Units.val_one, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem le_of_map_eq {p : ℕ} (hn3 : 3 ≤ n) (hZ : ∀ z ∈ scalars n K, z ^ p = 1 → z = 1)
    {E₀ E₁ : Subgroup (Matrix.SpecialLinearGroup (Fin n) K)} [IsElementaryAbelian p E₀]
    [IsElementaryAbelian p E₁]
    (h : E₁.map ((MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).comp (proj n K)) =
      E₀.map ((MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).comp (proj n K))) :
    E₁ ≤ E₀ := by
  have hinj := CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (k := K) hn3
  intro y hy
  have hmem : ((MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).comp (proj n K)) y ∈
      E₀.map ((MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).comp (proj n K)) := by
    rw [← h]
    exact ⟨y, hy, rfl⟩
  obtain ⟨x, hx, hxy⟩ := hmem
  have hproj : proj n K x = proj n K y := hinj hxy
  rw [proj_eq_proj_iff] at hproj
  set z := x⁻¹ * y with hz
  have hzc : z ∈ Subgroup.center _ := scalars_le_center n K hproj
  have hyz : y = x * z := by rw [hz, mul_inv_cancel_left]
  have hzp : z ^ p = 1 := by
    have h1 : (x * z) ^ p = x ^ p * z ^ p := Commute.mul_pow
      (Subgroup.mem_center_iff.mp hzc x) p
    rw [← hyz, elemPow_eq_one_of_isElementaryAbelian y hy,
      elemPow_eq_one_of_isElementaryAbelian x hx, one_mul] at h1
    exact h1.symm
  rw [hyz, hZ z hproj hzp, mul_one]
  exact hx

theorem linear_nonsplit_all_dimension_inner_plane_local_core_centralization {p ℓ f : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) (_hf : 1 ≤ f) (hn3 : 3 ≤ n)
    [Finite K] [CharP K ℓ] (hK : Nat.card K = ℓ ^ f) (hpq : ¬ p ∣ ℓ ^ f - 1)
    (B : Subgroup (MulAut (projectiveSL n K)))
    (hB : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ B)
    (E : Subgroup (MulAut (projectiveSL n K)))
    (hEH : E ≤ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range)
    [IsElementaryAbelian p E] (hEcard : Nat.card E = p ^ 2) :
    (∃! E₀ : Subgroup (Matrix.SpecialLinearGroup (Fin n) K),
      IsElementaryAbelian p E₀ ∧ Nat.card E₀ = p ^ 2 ∧
        E₀.map ((MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).comp
          (proj n K)) = E ∧
        Set.InjOn ((MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).comp
          (proj n K)) E₀) ∧
    ∀ E₀ : Subgroup (Matrix.SpecialLinearGroup (Fin n) K), IsElementaryAbelian p E₀ →
      E₀.map ((MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).comp
        (proj n K)) = E →
      ∀ a ∈ E₀, a ≠ 1 →
        (∀ h ∈ primaryFactors ((slGL n K a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
            Module.End K (Fin n → K)),
          linearSpecialBlock (slGL n K a) h ≤ (slGL n K).range ∧
          (linearSpecialBlock (slGL n K a) h).comap (slGL n K) ≤ Subgroup.centralizer {a} ∧
          (((linearSpecialBlock (slGL n K a) h).comap (slGL n K)).subgroupOf
            (Subgroup.centralizer {a})).Normal ∧
          (primaryMultiplicity ((slGL n K a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
              Module.End K (Fin n → K)) h = 1 → linearSpecialBlock (slGL n K a) h = ⊥) ∧
          (3 ≤ primaryMultiplicity ((slGL n K a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
              Module.End K (Fin n → K)) h ∨
            (primaryMultiplicity ((slGL n K a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
              Module.End K (Fin n → K)) h = 2 ∧ 3 < Nat.card (AdjoinRoot h)) →
            ((linearSpecialBlock (slGL n K a) h).comap (slGL n K)).map
                ((MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).comp
                  (proj n K)) ≤ B ⊓ Subgroup.centralizer {MulAut.conj (proj n K a)} ∧
            CFSG.IsComponent ((((linearSpecialBlock (slGL n K a) h).comap (slGL n K)).map
                ((MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).comp
                  (proj n K))).subgroupOf
              (B ⊓ Subgroup.centralizer {MulAut.conj (proj n K a)})) ∧
            ((linearSpecialBlock (slGL n K a) h).comap (slGL n K)).map
                ((MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).comp
                  (proj n K)) ≤
              (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ⊓
                Subgroup.centralizer {MulAut.conj (proj n K a)} ∧
            ((((linearSpecialBlock (slGL n K a) h).comap (slGL n K)).map
                ((MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).comp
                  (proj n K))).subgroupOf
              ((MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ⊓
                Subgroup.centralizer {MulAut.conj (proj n K a)})).Normal ∧
            ∀ s ∈ inSubgroup (aschbacherSolvableCore p)
                (B ⊓ Subgroup.centralizer {MulAut.conj (proj n K a)}),
              ∀ j ∈ ((linearSpecialBlock (slGL n K a) h).comap (slGL n K)).map
                ((MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).comp (proj n K)),
                s * j = j * s)) ∧
        (⨆ (h : K[X]) (_ : h ∈ primaryFactors ((slGL n K a :
              LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) ∧
            (3 ≤ primaryMultiplicity ((slGL n K a : LinearMap.GeneralLinearGroup K
                (Fin n → K)) : Module.End K (Fin n → K)) h ∨
              (primaryMultiplicity ((slGL n K a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
                Module.End K (Fin n → K)) h = 2 ∧ 3 < Nat.card (AdjoinRoot h)))),
            ((linearSpecialBlock (slGL n K a) h).comap (slGL n K)).map
              ((MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).comp
                (proj n K))) ≤
          (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ⊓
            Subgroup.centralizer {MulAut.conj (proj n K a)} ∧
        ((⨆ (h : K[X]) (_ : h ∈ primaryFactors ((slGL n K a :
              LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) ∧
            (3 ≤ primaryMultiplicity ((slGL n K a : LinearMap.GeneralLinearGroup K
                (Fin n → K)) : Module.End K (Fin n → K)) h ∨
              (primaryMultiplicity ((slGL n K a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
                Module.End K (Fin n → K)) h = 2 ∧ 3 < Nat.card (AdjoinRoot h)))),
            ((linearSpecialBlock (slGL n K a) h).comap (slGL n K)).map
              ((MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).comp
                (proj n K))).subgroupOf
          ((MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ⊓
            Subgroup.centralizer {MulAut.conj (proj n K a)})).Normal ∧
        ∀ s ∈ inSubgroup (aschbacherSolvableCore p)
            (B ⊓ Subgroup.centralizer {MulAut.conj (proj n K a)}),
          ∀ e ∈ E, s * e = e * s := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hn0 : 0 < n := by omega
  have hinj := CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (k := K) hn3
  set φ := (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).comp (proj n K)
    with hφ
  have hpq' : ¬ p ∣ Nat.card K - 1 := by rwa [hK]
  have hZ : ∀ z ∈ scalars n K, z ^ p = 1 → z = 1 := fun z hz hzp =>
    eq_one_of_mem_scalars hp hpq' hn0 hz hzp
  have hpk : (p : K) ≠ 0 := fun h0 =>
    hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp ((CharP.cast_eq_zero_iff K ℓ p).mp h0))
  have hker : φ.ker = scalars n K := by
    ext g
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, ← proj_eq_one_iff]
    exact ⟨fun h => hinj (by rw [h, map_one]), fun h => by rw [h, map_one]⟩
  have hkerp : ¬ p ∣ Nat.card φ.ker := by
    intro hdvd
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := φ.ker) p hdvd
    have hz1 : (z : Matrix.SpecialLinearGroup (Fin n) K) = 1 := by
      have hz' : (z : Matrix.SpecialLinearGroup (Fin n) K) ∈ scalars n K := hker.le z.2
      refine hZ z hz' ?_
      have := pow_orderOf_eq_one z
      rw [hz] at this
      exact congrArg Subtype.val this
    have : z = 1 := Subtype.ext hz1
    rw [this, orderOf_one] at hz
    exact hp.one_lt.ne hz
  have hinjOn : ∀ E₀ : Subgroup (Matrix.SpecialLinearGroup (Fin n) K),
      IsElementaryAbelian p E₀ → Set.InjOn φ E₀ := by
    intro E₀ hE₀ x hx y hy hxy
    have := hE₀
    have hproj : proj n K x = proj n K y := hinj hxy
    rw [proj_eq_proj_iff] at hproj
    have hzp : (x⁻¹ * y) ^ p = 1 := by
      rw [(Commute.inv_left (mul_comm_of_mem_elementaryAbelian (p := p) hx hy)).mul_pow,
        inv_pow, elemPow_eq_one_of_isElementaryAbelian x hx,
        elemPow_eq_one_of_isElementaryAbelian y hy, inv_one, one_mul]
    have := hZ _ hproj hzp
    rw [inv_mul_eq_one] at this
    exact this
  refine ⟨?_, fun E₀ hE₀ hmap a haE _ha1 => ?_⟩
  ·
    have hE : E ≤ φ.range := by
      intro e he
      obtain ⟨t, rfl⟩ := hEH he
      obtain ⟨g, rfl⟩ := proj_surjective n K t
      exact ⟨g, rfl⟩
    obtain ⟨E₀, hE₀, hE₀card, hE₀map⟩ :=
      CFSG.RankThree.PartOne.exists_lift_elementaryAbelian φ hp hkerp E hE hEcard
    refine ⟨E₀, ⟨hE₀, hE₀card, hE₀map, hinjOn E₀ hE₀⟩, ?_⟩
    rintro E₁ ⟨hE₁, -, hE₁map, -⟩
    have := hE₀
    have := hE₁
    exact le_antisymm (le_of_map_eq hn3 hZ (hE₁map.trans hE₀map.symm))
      (le_of_map_eq hn3 hZ (hE₀map.trans hE₁map.symm))
  · have := hE₀
    have hap : a ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian a haE
    have hsq := squarefree_minpoly_slGL hpk hap
    have hcomp := fun (h : K[X]) (hh : h ∈ primaryFactors ((slGL n K a :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)))
      (hg : 3 ≤ primaryMultiplicity ((slGL n K a : LinearMap.GeneralLinearGroup K
          (Fin n → K)) : Module.End K (Fin n → K)) h ∨
        (primaryMultiplicity ((slGL n K a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
          Module.End K (Fin n → K)) h = 2 ∧ 3 < Nat.card (AdjoinRoot h))) =>
      linearSpecialBlock_image_component hp hn3 hZ hB hap hsq hh
        (hg.imp id fun h2 => ⟨h2.1.ge, h2.2⟩)
    refine ⟨fun h hh => ⟨linearSpecialBlock_le_range_slGL hsq hh,
      comap_linearSpecialBlock_le_centralizer h, ⟨fun g hg c => ?_⟩,
      fun hm => ?_, fun hg => ?_⟩, iSup₂_le fun h hh => (hcomp h hh.1 hh.2).1, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf] at hg ⊢
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
        conj_mem_comap_linearSpecialBlock c.2 hg
    · exact linearSpecialBlock_eq_bot hsq hh hm
    · obtain ⟨hJC, hJn, hJL, hJcomp, hJS⟩ := hcomp h hh hg
      refine ⟨hJL, hJcomp, hJC, ⟨fun j hj c => ?_⟩, hJS⟩
      rw [Subgroup.mem_subgroupOf] at hj ⊢
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hJn c c.2 j hj
    ·
      refine ⟨fun d hd c => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hd ⊢
      have hle : (⨆ (h : K[X]) (_ : h ∈ primaryFactors ((slGL n K a :
              LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) ∧
            (3 ≤ primaryMultiplicity ((slGL n K a : LinearMap.GeneralLinearGroup K
                (Fin n → K)) : Module.End K (Fin n → K)) h ∨
              (primaryMultiplicity ((slGL n K a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
                Module.End K (Fin n → K)) h = 2 ∧ 3 < Nat.card (AdjoinRoot h)))),
            ((linearSpecialBlock (slGL n K a) h).comap (slGL n K)).map φ) ≤
          (⨆ (h : K[X]) (_ : h ∈ primaryFactors ((slGL n K a :
              LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) ∧
            (3 ≤ primaryMultiplicity ((slGL n K a : LinearMap.GeneralLinearGroup K
                (Fin n → K)) : Module.End K (Fin n → K)) h ∨
              (primaryMultiplicity ((slGL n K a : LinearMap.GeneralLinearGroup K (Fin n → K)) :
                Module.End K (Fin n → K)) h = 2 ∧ 3 < Nat.card (AdjoinRoot h)))),
            ((linearSpecialBlock (slGL n K a) h).comap (slGL n K)).map φ).comap
              (MulAut.conj (c : MulAut (projectiveSL n K))).toMonoidHom := by
        refine iSup₂_le fun h hh j hj => ?_
        rw [Subgroup.mem_comap]
        exact Subgroup.mem_iSup_of_mem h (Subgroup.mem_iSup_of_mem hh
          ((hcomp h hh.1 hh.2).2.1 c c.2 j hj))
      have h1 := hle hd
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h1
    ·
      rintro s hs e he
      rw [← hmap] at he
      obtain ⟨v, hv, rfl⟩ := he
      exact core_commute_elementaryAbelian hp hp3 hn3 hpk hZ E₀ hB haE s hs v hv

end CFSG.RankThree.CALinearPrimary
