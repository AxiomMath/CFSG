module

public import CFSG.RankThree.PartTwo.Sec15.F153L3C2Gen
public import CFSG.RankThree.PartTwo.Sec15.F153L3C2Local

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153L3C2

open CFSG CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_conj_mem' {B T : Subgroup G}
    (h : ∀ g ∈ B, ∀ y ∈ T, g * y * g⁻¹ ∈ T) : B ≤ Subgroup.normalizer (T : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact h g hg y
  · intro hy
    have := h g⁻¹ (B.inv_mem hg) _ hy
    simpa [mul_assoc] using this

theorem rho_conj_mem_innQ {Y : Subgroup G} {n a : ↥(Subgroup.normalizer (Y : Set G))}
    (h : rho Y n ∈ innQ Y) : rho Y (a * n * a⁻¹) ∈ innQ Y := by
  obtain ⟨q, hq⟩ := h
  refine ⟨rho Y a q, ?_⟩
  rw [map_mul, map_mul, map_inv, ← hq]
  ext z
  simp [MulAut.conj_apply]

theorem isElemAbelian_mono' {A B : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A) (hBA : B ≤ A) :
    CFSG.Assembly.IsElemAbelian 3 B := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hA.2 x (hBA hx)⟩
  haveI := hA.1
  exact Subtype.ext (setLike_mul_comm (hBA a.2) (hBA b.2))

theorem inner_trivial_153 (hKF : KFactL3CentOdd) {f : ℕ} (hf : 1 ≤ f) {A Y S : Subgroup G}
    {LB : Subgroup G → Subgroup G} (hA : IsE27 A) (hLB : ∀ B, IsHyperplane A B → LB B = ⊥)
    (hSQ : S ∈ scriptQ A LB) (hS2 : IsPGroup 2 S) (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hSY : S ≤ Subgroup.normalizer (Y : Set G))
    (hq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (hε : IsLThreeEpsAt ((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) 2 f) :
    ∀ n : ↥(Subgroup.normalizer (Y : Set G)), (n : G) ∈ S → rho Y n ∈ innQ Y → rho Y n = 1 := by
  classical
  set N : Subgroup G := Subgroup.normalizer (Y : Set G) with hN
  set T : Subgroup G := S ⊓ ((innQ Y).comap (rho Y)).map N.subtype with hT
  have hmemT : ∀ t : G, t ∈ T ↔ t ∈ S ∧ ∃ m : ↥N, rho Y m ∈ innQ Y ∧ (m : G) = t := by
    intro t
    simp only [hT, Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.subtype_apply]
  have hTS : T ≤ S := inf_le_left
  have hT2 : IsPGroup 2 T := hS2.to_le hTS
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hSQ.1.2.2
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := by
    refine le_normalizer_of_conj_mem' fun a ha t ht => ?_
    obtain ⟨htS, m, hm, rfl⟩ := (hmemT t).mp ht
    refine (hmemT _).mpr ⟨(Subgroup.mem_normalizer_iff.mp (hAS ha) _).mp htS,
      (⟨a, hAY ha⟩ : ↥N) * m * (⟨a, hAY ha⟩ : ↥N)⁻¹, rho_conj_mem_innQ hm, ?_⟩
    simp
  have hq3 : ∀ B, IsHyperplane A B → T ⊓ Subgroup.centralizer (B : Set G) ≤
      pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
    intro B hB
    have h2 : S ⊓ Subgroup.centralizer (B : Set G) ≤ qBound A LB B := hSQ.2 B hB
    rw [qBound, hLB B hB, sup_bot_eq] at h2
    exact (inf_le_inf_right _ hTS).trans h2
  have hgen := le_sup_pPrimeCore_of_hyperplanes hA.1 (by rw [hA.2]; norm_num) hT2 hAT hq3
  set K : Subgroup G := (rho Y).ker.map N.subtype with hK
  have hloc : ∀ D : Subgroup G, D ≤ A →
      ∀ x ∈ T ⊓ pPrimeCoreOf 3 (Subgroup.centralizer (D : Set G)), x ∈ K := by
    intro D hDA x hx
    obtain ⟨hxT, hxD⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxS, m, hm, rfl⟩ := (hmemT x).mp hxT
    have hx2 : ∃ k : ℕ, (m : G) ^ (2 ^ k) = 1 := by
      obtain ⟨k, hk⟩ := hS2 ⟨(m : G), hxS⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have h1 : rho Y m = 1 :=
      rho_eq_one_of_inner_local hKF hf hq hε (hDA.trans hAY) (isElemAbelian_mono' hA.1 hDA) m.2
        hx2 hxD hm
    exact ⟨m, h1, rfl⟩
  have hTK : T ≤ K := by
    refine hgen.trans (sup_le ?_ ?_)
    · exact iSup₂_le fun B hB x hx => hloc B hB.1 x hx
    · exact fun x hx => hloc A le_rfl x hx
  intro n hnS hnin
  have hnT : (n : G) ∈ T := (hmemT _).mpr ⟨hnS, n, hnin, rfl⟩
  obtain ⟨m, hm1, hmn⟩ := hTK hnT
  have hmn' : m = n := Subtype.ext hmn
  rw [← hmn']
  exact hm1

end CFSG.RankThree.PartTwo.Sec15.F153L3C2
