module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDGen
import CFSG.LocalAnalysis.StandardType.GGSecFiveNbrGenKNOfInputs

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo

section Pure

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ggRankOne_le_ggRankTwo (Bs : Subgroup G) (r r' : MulAut ↥Bs) :
    ggRankOne Bs r ≤ ggRankTwo Bs r r' := by
  refine Subgroup.closure_mono ?_
  rintro y ⟨hy, k, hk⟩
  have hsub : ((ggHyperplane Bs r ⊓ ggHyperplane Bs r' : Subgroup G) : Set G) ⊆
      (ggHyperplane Bs r : Set G) := SetLike.coe_subset_coe.mpr inf_le_left
  exact ⟨Subgroup.centralizer_le hsub hy, k, hk⟩

theorem exists_two_power_inducing {Bs : Subgroup G} {r : MulAut ↥Bs} (hr : r ^ 2 = 1) {g : G}
    (hg : ∀ b : ↥Bs, ((r b : ↥Bs) : G) = g * b * g⁻¹) :
    ∃ h ∈ Subgroup.zpowers g, (∃ k : ℕ, h ^ (2 ^ k) = 1) ∧
      ∀ b : ↥Bs, ((r b : ↥Bs) : G) = h * b * h⁻¹ := by
  obtain ⟨k, u, hu, hN⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0
    have hrN : r ^ orderOf g = 1 := by
      refine MulEquiv.ext fun b => Subtype.ext ?_
      have h1 := s2jn_pow_induced hg (orderOf g)
      rw [pow_orderOf_eq_one] at h1
      simpa using h1 b
    obtain ⟨s, hs⟩ := hu
    have hord : orderOf g = 2 * s + 1 := by rw [hN, hs]; simp
    have hr1 : r = 1 := by
      rw [hord, pow_succ, pow_mul, hr, one_pow, one_mul] at hrN
      exact hrN
    refine ⟨1, one_mem _, ⟨0, by simp⟩, fun b => ?_⟩
    simp [hr1]
  · have hcop : Nat.Coprime (2 ^ k) u := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hu)
    obtain ⟨t, ht1, ht0⟩ := Nat.chineseRemainder hcop 1 0
    have hut : u ∣ t := (Nat.modEq_zero_iff_dvd).mp ht0
    have ht2 : t ≡ 1 [MOD 2] := ht1.of_dvd (dvd_pow_self 2 hk0.ne')
    obtain ⟨s, hs⟩ : Odd t := Nat.odd_iff.mpr (by simpa [Nat.ModEq] using ht2)
    have hrt : r ^ t = r := by rw [hs, pow_succ, pow_mul, hr, one_pow, one_mul]
    refine ⟨g ^ t, ⟨(t : ℤ), by simp⟩, ⟨k, ?_⟩, fun b => ?_⟩
    · rw [← pow_mul]
      refine orderOf_dvd_iff_pow_eq_one.mp ?_
      obtain ⟨c, hc⟩ := hut
      exact ⟨c, by rw [hN, hc]; ring⟩
    · have h1 := s2jn_pow_induced hg t b
      rwa [hrt] at h1

theorem exists_mem_ggRankOne_inducing {Bs : Subgroup G} {r : MulAut ↥Bs} (hr : r ^ 2 = 1) {g : G}
    (hg : ∀ b : ↥Bs, ((r b : ↥Bs) : G) = g * b * g⁻¹) :
    ∃ h ∈ Subgroup.zpowers g, h ∈ ggRankOne Bs r ∧
      ∀ b : ↥Bs, ((r b : ↥Bs) : G) = h * b * h⁻¹ := by
  obtain ⟨h, hh, ⟨k, hk⟩, hind⟩ := exists_two_power_inducing hr hg
  have hcent : h ∈ Subgroup.centralizer (ggHyperplane Bs r : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    have hrb : r b = b := hb
    have h1 := hind b
    rw [hrb] at h1
    calc ((b : ↥Bs) : G) * h = (h * b * h⁻¹) * h := by rw [← h1]
      _ = h * b := by group
  exact ⟨h, hh, Subgroup.subset_closure ⟨hcent, k, hk⟩, hind⟩

theorem mem_ggAutomizer_of_rankOne_le {Y P Bs : Subgroup G} {r : MulAut ↥Bs} (hr : r ^ 2 = 1)
    (hY : r ∈ ggAutomizer Y Bs) (hP : ggRankOne Bs r ≤ P) : r ∈ ggAutomizer P Bs := by
  obtain ⟨g, -, hgN, hg⟩ := mem_ggAutomizer_iff.mp hY
  obtain ⟨h, hh, hhS, hind⟩ := exists_mem_ggRankOne_inducing hr hg
  exact mem_ggAutomizer_iff.mpr ⟨h, hP hhS, (Subgroup.zpowers_le.mpr hgN) hh, hind⟩

theorem ggAutomizerJoin_le_ggAutomizer_of_rankOne_le {L Bs P : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : ∀ t : ι, ggRankOne Bs ((e (M.simple t) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ≤ P) :
    ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer P Bs := by
  let φ : M.Group →* MulAut ↥Bs := (ggAutomizerJoin L Bs 𝒦).subtype.comp e.toMonoidHom
  have hcl : Subgroup.closure (Set.range M.simple) = ⊤ :=
    M.toCoxeterSystem.subgroup_closure_range_simple
  have hle : Subgroup.closure (Set.range M.simple) ≤ (ggAutomizer P Bs).comap φ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨t, rfl⟩
    have hss : M.simple t * M.simple t = 1 := M.toCoxeterSystem.simple_mul_simple_self t
    have hr2 : (φ (M.simple t)) ^ 2 = 1 := by rw [← map_pow, pow_two, hss, map_one]
    exact mem_ggAutomizer_of_rankOne_le hr2
      (ggAutomizerJoin_le_ggAutomizer L Bs 𝒦 (e (M.simple t)).2) (hP t)
  intro a ha
  have hw : e.symm ⟨a, ha⟩ ∈ (ggAutomizer P Bs).comap φ := hle (by rw [hcl]; trivial)
  have hφ : φ (e.symm ⟨a, ha⟩) = a := by
    show (((e (e.symm ⟨a, ha⟩) : ↥(ggAutomizerJoin L Bs 𝒦))) : MulAut ↥Bs) = a
    rw [MulEquiv.apply_symm_apply]
  rw [← hφ]
  exact hw

theorem qtwoNode_le_iSup {Bs : Subgroup G} {m : ℕ} (r : Fin m → MulAut ↥Bs) (hm : 2 ≤ m)
    (i : Fin m) : qtwoNode Bs r i ≤ ⨆ (i : Fin m) (j : Fin m) (_ : i < j), qtwoW Bs r i j := by
  have hle : ∀ {i j : Fin m}, i ≠ j → qtwoNode Bs r i ≤ qtwoW Bs r i j := by
    intro i j hij
    rcases ggCoxeterMatrixD_two_or_three i j hij with h2 | h3
    · rw [qtwoW_of_nonedge r h2]
      exact le_sup_left
    · rw [qtwoW_of_edge r h3]
      exact ggRankOne_le_ggRankTwo Bs _ _
  by_cases h : (i : ℕ) + 1 < m
  · have hij : i < (⟨i + 1, h⟩ : Fin m) := by simp [Fin.lt_def]
    exact (hle hij.ne).trans (le_iSup_of_le i (le_iSup_of_le ⟨i + 1, h⟩
      (le_iSup (fun _ : i < (⟨i + 1, h⟩ : Fin m) => qtwoW Bs r i ⟨i + 1, h⟩) hij)))
  · obtain ⟨j0, hj0⟩ : ∃ j0 : Fin m, j0 = ⟨0, by omega⟩ := ⟨_, rfl⟩
    have hji : j0 < i := by
      subst hj0
      simp only [Fin.lt_def]
      omega
    calc qtwoNode Bs r i ≤ qtwoW Bs r i j0 := hle hji.ne'
      _ = qtwoW Bs r j0 i := qtwoW_symm Bs r _ _
      _ ≤ ⨆ (i : Fin m) (j : Fin m) (_ : i < j), qtwoW Bs r i j :=
        le_iSup_of_le j0 (le_iSup_of_le i (le_iSup (fun _ : j0 < i => qtwoW Bs r j0 i) hji))

end Pure

section Cfg

variable {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type}
  {M : CoxeterMatrix ι} (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)) {m : ℕ}

theorem ggAutomizerJoin_le_ggAutomizer_nodes (hm : 2 ≤ m) (e' : Fin m ≃ ι) :
    ggAutomizerJoin L Bs 𝒦 ≤
      ggAutomizer (⨆ (i : Fin m) (j : Fin m) (_ : i < j), qtwoW Bs (qtwoRefl e e') i j) Bs := by
  refine ggAutomizerJoin_le_ggAutomizer_of_rankOne_le e fun t => ?_
  obtain ⟨i, rfl⟩ := e'.surjective t
  exact qtwoNode_le_iSup (qtwoRefl e e') hm i

end Cfg

section Inputs


@[expose] def GGQTwoSelLInputOn (R : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) (ι : Type) (M : CoxeterMatrix ι)
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)), GGQTwoDCfg p B Bs x L D J 𝒦 M e →
      ∀ (m : ℕ) (e' : Fin m ≃ ι), R m → M = (ggCoxeterMatrixD m).reindex e' →
        L ≤ (⨆ (i : Fin m) (j : Fin m) (_ : i < j), qtwoW Bs (qtwoRefl e e') i j)

@[expose] def GGQTwoSelLInput : Prop :=
  GGQTwoSelLInputOn fun m => 7 ≤ m

theorem ggQTwoGenInput_of_absorb {R : ℕ → Prop} (hR : ∀ m, R m → 2 ≤ m)
    (hNonc : GGLNoncyclicInput) (hRM : GGQTwoRMInputOn R) (hGN : GGQTwoGNInputOn R)
    (hSel : GGQTwoSelLInputOn R) (hEdge : GGQTwoEdgeLeInputOn R) : GGQTwoGenInputOn R := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1.1
  have hLP := hSel G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM
  have hA := ggAutomizerJoin_le_ggAutomizer_nodes e (hR m hm) e'
  refine le_antisymm (iSup_le fun i => iSup_le fun j => iSup_le fun hij => ?_) ?_
  · exact hEdge G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM i j hij.ne
  · refine ggG0_le_of hLP fun y K' hK' => ?_
    have hRMK := hRM G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM y K' hK'
    have hgen := hGN G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM y K' hK' hRMK
    refine GGConfig.le_of_ggAutomizer_le hNonc hconf hLP ?_ (hRMK.trans hA)
    refine hgen.trans (iSup_le fun n => iSup_le fun hn => iSup_le fun hφ => ?_)
    obtain ⟨φ, hnN, -⟩ := hφ
    exact le_iSup_of_le n (le_iSup
      (fun _ : n ∈ K' ⊓ Subgroup.normalizer (Bs : Set G) => J.map (MulAut.conj n).toMonoidHom)
      ⟨hn, hnN⟩)

end Inputs

end CFSG.StandardType.QTwo

end
