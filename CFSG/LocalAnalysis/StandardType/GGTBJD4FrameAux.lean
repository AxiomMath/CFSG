module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosPrimed
import CFSG.LocalAnalysis.StandardType.GGStdPosTorusFix
import CFSG.LocalAnalysis.StandardType.GGStdPosTagData

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

theorem ggTBJD4_exists_y {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {x : G}
    {L D : Subgroup G} (hxD : x ∈ D) (hx1 : x ≠ 1) (hDel : IsElemAbelian p D)
    (hDcard : Nat.card D = p ^ 2) (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) :
    ∃ y ∈ D, y ∉ Subgroup.zpowers x ∧ Subgroup.closure {x, y} = D ∧
      L ⊓ Subgroup.centralizer (D : Set G) = L ⊓ Subgroup.centralizer ({y} : Set G) := by
  have hxp : x ^ p = 1 := hDel.2 x hxD
  have hz : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (p := p) (hp := Fact.mk hp) hxp hx1
  obtain ⟨y, hyD, hyz⟩ : ∃ y ∈ D, y ∉ Subgroup.zpowers x := by
    by_contra h
    push Not at h
    have hle : D ≤ Subgroup.zpowers x := fun y hy => h y hy
    have := Subgroup.card_le_of_le hle
    rw [hDcard, hz] at this
    have h2 := hp.two_le
    nlinarith
  set H : Subgroup G := Subgroup.closure {x, y} with hH
  have hHD : H ≤ D := (Subgroup.closure_le _).mpr (by
    intro g hg
    rcases hg with rfl | rfl
    · exact hxD
    · exact hyD)
  have hzH : Subgroup.zpowers x ≤ H :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hyH : y ∈ H := Subgroup.subset_closure (by simp)
  have hHD' : H = D := by
    apply Subgroup.eq_of_le_of_card_ge hHD
    have hdvd : Nat.card H ∣ p ^ 2 := by
      rw [← hDcard]; exact Subgroup.card_dvd_of_le hHD
    obtain ⟨k, hk, hkH⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hpH : p ∣ Nat.card H := by rw [← hz]; exact Subgroup.card_dvd_of_le hzH
    interval_cases k
    · rw [pow_zero] at hkH
      rw [hkH] at hpH
      exact absurd (Nat.le_of_dvd one_pos hpH) (by have := hp.two_le; omega)
    · exfalso
      rw [pow_one] at hkH
      have : Subgroup.zpowers x = H :=
        Subgroup.eq_of_le_of_card_ge hzH (by rw [hz, hkH])
      exact hyz (this ▸ hyH)
    · rw [hkH, hDcard]
  have hcent : L ⊓ Subgroup.centralizer (D : Set G) =
      L ⊓ Subgroup.centralizer ({y} : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hyD))
    · rintro g ⟨hgL, hgy⟩
      refine ⟨hgL, ?_⟩
      show g ∈ Subgroup.centralizer (D : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hh' : h ∈ H := by rw [hHD']; exact hh
      refine Subgroup.closure_induction (p := fun h _ => h * g = g * h) ?_ ?_ ?_ ?_ hh'
      · intro a ha
        rcases ha with rfl | rfl
        · exact (Subgroup.mem_centralizer_iff.mp (hLx hgL)) a rfl
        · exact (Subgroup.mem_centralizer_iff.mp hgy) a rfl
      · simp
      · intro a b _ _ ha hb
        rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
      · intro a _ ha
        calc a⁻¹ * g = a⁻¹ * (g * a) * a⁻¹ := by group
          _ = a⁻¹ * (a * g) * a⁻¹ := by rw [← ha]
          _ = g * a⁻¹ := by group
  refine ⟨y, hyD, hyz, ?_, hcent⟩
  rw [← hH]
  exact hHD'

theorem ggTBJD4_not_isCyclic {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {D : Subgroup G} (hDel : IsElemAbelian p D) (hDcard : Nat.card D = p ^ 2) : ¬ IsCyclic D := by
  rintro hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := D) (h := hcyc)
  have hgp : g ^ p = 1 := by
    apply Subtype.ext
    simpa using hDel.2 (g : G) g.2
  have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
  have hcard : orderOf g = p ^ 2 := by rw [hg, hDcard]
  have hpp : p ^ 2 ∣ p := hcard ▸ hdvd
  have hle : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos hpp
  nlinarith [hp.two_le]

theorem ggTBJD4_card_inf_le {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {x : G}
    {L D : Subgroup G} (hDcard : Nat.card D = p ^ 2) (hxD : x ∈ D) (hxL : x ∉ L) :
    Nat.card ↥(D ⊓ L) ≤ p := by
  obtain ⟨k, hk, hkc⟩ := (Nat.dvd_prime_pow hp).mp
    (show Nat.card ↥(D ⊓ L) ∣ p ^ 2 by
      rw [← hDcard]
      exact Subgroup.card_dvd_of_le inf_le_left)
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · rw [hkc]
    exact (Nat.pow_le_pow_right hp.pos (by omega : k ≤ 1)).trans_eq (pow_one p)
  exfalso
  have hDL : D ≤ L := inf_eq_left.mp (Subgroup.eq_of_le_of_card_ge inf_le_left
    (by rw [hkc, hDcard]; exact Nat.pow_le_pow_right hp.pos hk2))
  exact hxL (hDL hxD)

theorem ggTBJD4_count
    {G : Type} [Group G] [Finite G] {p f : ℕ} {Bs D J : Subgroup G}
    {ψ : (ggU .POmegaPlus 4 f).K →* G} (hinj : Function.Injective ψ)
    (hstd : GGKGPosStdPos (ggU .POmegaPlus 4 f).D ψ Bs)
    (hC3 : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hBJ : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) {J' : Subgroup (ggU .POmegaPlus 4 f).K}
    (hJ' : J'.map ψ = J) :
    Set.ncard {h | h ∈ ggTorus (ggU .POmegaPlus 4 f).D ∧ h ^ p = 1 ∧
      h ∈ Subgroup.centralizer (J' : Set (ggU .POmegaPlus 4 f).K)} ≤ Nat.card ↥(D ⊓ ψ.range) := by
  have h3 : 3 ≤ bnRank .POmegaPlus 4 := by norm_num [bnRank]
  obtain ⟨-, ⟨nn, H, hct, hext, hBU⟩, xp, C, O, hE⟩ :=
    ggStdPos_bruhatData (f := f) (t := .POmegaPlus) (n := 4) h3 (Or.inr (Or.inl rfl))
  have hker : ψ.ker ≤ Subgroup.center (ggU .POmegaPlus 4 f).K := by
    rw [(MonoidHom.ker_eq_bot_iff ψ).mpr hinj]
    exact bot_le
  have hmaps : ∀ h ∈ {h : (ggU .POmegaPlus 4 f).K |
      h ∈ ggTorus (ggU .POmegaPlus 4 f).D ∧ h ^ p = 1 ∧
        h ∈ Subgroup.centralizer (J' : Set (ggU .POmegaPlus 4 f).K)},
      ψ h ∈ ((D ⊓ ψ.range : Subgroup G) : Set G) := by
    intro h hh
    have hcentB : ψ h ∈ Subgroup.centralizer (Bs : Set G) :=
      ggStdPos_psi_mem_centralizer hct hext hBU hE ψ hker hstd h hh.1
    have hBs : ψ h ∈ Bs := hC3 _ hcentB (by rw [← map_pow, hh.2.1, map_one])
    have hJc : ψ h ∈ Subgroup.centralizer (J : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun j hj => ?_
      obtain ⟨j', hj', rfl⟩ :=
        Subgroup.mem_map.mp (show j ∈ J'.map ψ by rw [hJ']; exact hj)
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hh.2.2 j' hj']
    exact Subgroup.mem_inf.mpr ⟨hBJ (Subgroup.mem_inf.mpr ⟨hBs, hJc⟩), ⟨h, rfl⟩⟩
  have hinj' : Set.InjOn ψ {h : (ggU .POmegaPlus 4 f).K |
      h ∈ ggTorus (ggU .POmegaPlus 4 f).D ∧ h ^ p = 1 ∧
        h ∈ Subgroup.centralizer (J' : Set (ggU .POmegaPlus 4 f).K)} :=
    fun _ _ _ _ h => hinj h
  exact (Set.ncard_le_ncard_of_injOn ψ hmaps hinj' (Set.toFinite _)).trans_eq
    (by rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq])

end CFSG.StandardType

end
