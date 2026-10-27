module

public import CFSG.RankThree.PartTwo.Sec15.Ronan155DiamondL3Aut
public import CFSG.RankThree.PartTwo.Sec15.Ronan155DiamondL3Comm
public import CFSG.RankThree.PartTwo.KFacts.L34Sections
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
import CFSG.RankThree.PartTwo.Sec15.Gagen1521Four
import CFSG.RankThree.PartTwo.Sec4.Item462AltProofCases
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan155DiamondL3

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.RankThree.PartTwo.Sec14

theorem hasOrderFourMod_of_quotient {G : Type*} [Group G] [Finite G] {H N : Subgroup G}
    (hNH : N ≤ H) [(N.subgroupOf H).Normal] (hsimp : IsSimpleGroup (↥H ⧸ N.subgroupOf H))
    (h4 : ∃ s : ↥H ⧸ N.subgroupOf H, orderOf s = 4) : HasOrderFourMod H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup (↥H ⧸ N.subgroupOf H) := hsimp
  obtain ⟨s, hs⟩ := h4
  set π := QuotientGroup.mk' (N.subgroupOf H) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  refine ⟨N, hNH, fun D hDH hHD hD2 => ?_, ?_⟩
  · have hDn : (D.subgroupOf H).Normal := by
      refine ⟨fun a ha b => ?_⟩
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      have hb := hHD b.2
      rw [Subgroup.mem_normalizer_iff] at hb
      simpa using (hb a).mp ha
    have hD'n : ((D.subgroupOf H).map π).Normal := hDn.map π hπs
    have hD'2 : IsPGroup 2 ((D.subgroupOf H).map π) := by
      refine IsPGroup.map ?_ π
      intro x
      obtain ⟨k, hk⟩ := hD2 ⟨(x : H), x.2⟩
      exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
    haveI := hD'n
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((D.subgroupOf H).map π) with hbot | htop
    · intro x hx
      have hxD : (⟨x, hDH hx⟩ : H) ∈ D.subgroupOf H := Subgroup.mem_subgroupOf.mpr hx
      have h1 : π ⟨x, hDH hx⟩ ∈ (D.subgroupOf H).map π := Subgroup.mem_map_of_mem π hxD
      rw [hbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf] at h1
      exact h1
    · exfalso
      have hQ2 : IsPGroup 2 (↥H ⧸ N.subgroupOf H) := by
        intro q
        have hq : q ∈ (D.subgroupOf H).map π := by rw [htop]; exact Subgroup.mem_top q
        obtain ⟨k, hk⟩ := hD'2 ⟨q, hq⟩
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩
      haveI : Nontrivial (↥H ⧸ N.subgroupOf H) := hsimp.toNontrivial
      have hZ : Subgroup.center (↥H ⧸ N.subgroupOf H) = ⊤ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
          (Subgroup.center (↥H ⧸ N.subgroupOf H)) with h | h
        · exact absurd h (hQ2.bot_lt_center).ne'
        · exact h
      have hcomm : ∀ a b : ↥H ⧸ N.subgroupOf H, a * b = b * a := by
        intro a b
        have hb : b ∈ Subgroup.center (↥H ⧸ N.subgroupOf H) := by rw [hZ]; exact Subgroup.mem_top b
        exact Subgroup.mem_center_iff.mp hb a
      have hn : (Subgroup.zpowers (s ^ 2)).Normal :=
        ⟨fun a ha b => by rw [hcomm b a, mul_inv_cancel_right]; exact ha⟩
      haveI := hn
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers (s ^ 2)) with h | h
      · have h2 : s ^ 2 = 1 := by
          have := Subgroup.mem_zpowers (s ^ 2)
          rwa [h, Subgroup.mem_bot] at this
        have := orderOf_dvd_of_pow_eq_one h2
        rw [hs] at this
        norm_num at this
      · have hsz : s ∈ Subgroup.zpowers (s ^ 2) := by rw [h]; exact Subgroup.mem_top s
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hsz
        have h1 : s ^ (2 * k - 1) = 1 := by
          rw [_root_.zpow_sub, _root_.zpow_mul, zpow_one, zpow_ofNat, hk, mul_inv_cancel]
        have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
        rw [hs] at h2
        omega
  · obtain ⟨⟨y₀, hy₀⟩, rfl⟩ := hπs s
    have hk0 : orderOf y₀ ≠ 0 := (orderOf_pos y₀).ne'
    obtain ⟨b, m, hm, hbm⟩ := Nat.exists_eq_two_pow_mul_odd hk0
    refine ⟨y₀ ^ m, pow_mem hy₀ m, ⟨b, ?_⟩, fun hN => ?_⟩
    · rw [← pow_mul, mul_comm, ← hbm, pow_orderOf_eq_one]
    · have h1 : π ⟨y₀, hy₀⟩ ^ (2 * m) = 1 := by
        rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
          Subgroup.mem_subgroupOf, SubmonoidClass.coe_pow, mul_comm, pow_mul]
        exact hN
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hs] at h2
      obtain ⟨t, ht⟩ := hm
      omega

theorem HasOrderFourMod.map_equiv {G G' : Type*} [Group G] [Group G'] {H : Subgroup G}
    (hH : HasOrderFourMod H) (e : G ≃* G') : HasOrderFourMod (H.map e.toMonoidHom) := by
  obtain ⟨N, hNH, hDN, y, hyH, ⟨k, hyk⟩, hy2⟩ := hH
  refine ⟨N.map e.toMonoidHom, Subgroup.map_mono hNH, fun D hDH hHD hD2 => ?_,
    e y, Subgroup.mem_map_of_mem _ hyH, ⟨k, by rw [← map_pow]; simp [hyk]⟩, ?_⟩
  · have hDc : D.comap e.toMonoidHom ≤ H := by
      intro x hx
      have := hDH hx
      rw [Subgroup.mem_map_equiv] at this
      simpa using this
    have hHDc : H ≤ Subgroup.normalizer ((D.comap e.toMonoidHom : Subgroup G) : Set G) := by
      intro x hx
      have hx' := hHD (Subgroup.mem_map_of_mem e.toMonoidHom hx)
      rw [Subgroup.mem_normalizer_iff] at hx' ⊢
      intro d
      rw [Subgroup.mem_comap, Subgroup.mem_comap, hx' (e.toMonoidHom d), map_mul, map_mul, map_inv]
    have hD2c : IsPGroup 2 (D.comap e.toMonoidHom) :=
      hD2.comap_of_injective e.toMonoidHom e.injective
    have hle := hDN _ hDc hHDc hD2c
    intro x hx
    refine ⟨e.symm x, hle ?_, by simp⟩
    rw [Subgroup.mem_comap]
    simpa using hx
  · intro hmem
    apply hy2
    rw [← map_pow] at hmem
    obtain ⟨z, hz, hze⟩ := hmem
    have : z = y ^ 2 := e.injective hze
    rwa [← this]

theorem exists_comm_pow_twelve_ne_one {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 4 ≤ f) {H : Subgroup (projectiveSL 3 K)}
    (hH : HasOrderFourMod H) (hperf : ⁅H, H⁆ = H) {β : MulAut (projectiveSL 3 K)}
    (hβ2 : β ^ 2 = 1) (hβ1 : β ≠ 1) (hβH : ∀ h ∈ H, β h = h) :
    ∃ j : projectiveSL 3 K, (β j * j⁻¹) ^ 12 ≠ 1 := by
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := K) (n := 3) le_rfl).2 β
  have hσ := fieldAut_ne_one_of_fix hH hperf hε hβH hβ1
  have key : ∀ (M : GL (Fin 3) K) (τ : MulAut (projectiveSL 3 K)) (j₀ : projectiveSL 3 K),
      (τ j₀ * j₀⁻¹) ^ 12 ≠ 1 →
        ((conjAut 3 K M * τ * (conjAut 3 K M)⁻¹) (conjAut 3 K M j₀) *
          (conjAut 3 K M j₀)⁻¹) ^ 12 ≠ 1 := by
    intro M τ j₀ hj
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, ← map_inv, ← map_mul, ← map_pow]
    intro h
    exact hj ((MulEquiv.map_eq_one_iff _).mp h)
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  · rw [pow_zero, mul_one] at hβ2 ⊢
    obtain ⟨hfe, hσx, M, hM⟩ :=
      even_linear_field_involution_descent (by omega) hK le_rfl A σ hσ hβ2
    obtain ⟨j₀, hj₀⟩ := exists_fieldAut_comm_pow_twelve_ne_one hK hf hfe hσx
    exact ⟨conjAut 3 K M j₀, by rw [hM]; exact key M _ j₀ hj₀⟩
  · rw [pow_one] at hβ2 ⊢
    obtain ⟨hfe, hσx, M, hM⟩ := UnitaryHigher.linear_graph_field_involution_descent Nat.prime_two
      (by omega) hK le_rfl A σ hσ hβ2
    obtain ⟨j₀, hj₀⟩ := exists_fieldAut_mul_dualAut_comm_pow_twelve_ne_one hK hf hfe hσx
    exact ⟨conjAut 3 K M j₀, by rw [hM]; exact key M _ j₀ hj₀⟩

theorem kfSubL3_holds :
    ∀ (n m : ℕ), 2 ≤ n → 1 ≤ m →
    ∀ (H N : Subgroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 (2 * n * m)))),
      ⁅H, H⁆ = H → N ≤ H → ∀ [(N.subgroupOf H).Normal], IsPGroup 2 N →
      IsLThreeEpsAt (↥H ⧸ N.subgroupOf H) 2 n →
      (∀ U : Subgroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 (2 * n * m))),
          IsPGroup 2 U → H ≤ Subgroup.normalizer (U : Set ↥(CFSG.Assembly.RankThreeEven.projSL 3
            (GaloisField 2 (2 * n * m)))) → U = ⊥) ∧
      Subgroup.centralizer
        (H : Set ↥(CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 (2 * n * m)))) = ⊥ ∧
      (∀ α β : MulAut (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 (2 * n * m))),
          α ^ 2 = 1 → β ^ 2 = 1 → α ≠ 1 → β ≠ 1 → (∀ h ∈ H, α h = h) → (∀ h ∈ H, β h = h) →
            α = β) ∧
      (∀ β : MulAut (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 (2 * n * m))),
          β ^ 2 = 1 → β ≠ 1 → (∀ h ∈ H, β h = h) → ∃ j, (β j * j⁻¹) ^ 12 ≠ 1) := by
  intro n m hn hm H N hperf hNH _ _ hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := GaloisField 2 (2 * n * m)
  have hf0 : 2 * n * m ≠ 0 := by positivity
  have hK : Nat.card K = 2 ^ (2 * n * m) := GaloisField.card 2 (2 * n * m) hf0
  have hf4 : 4 ≤ 2 * n * m := by nlinarith
  set e := CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3 K with he
  haveI : Finite (CFSG.Assembly.RankThreeEven.projSL 3 K) := Finite.of_equiv _ e.symm.toEquiv
  have hsimp : IsSimpleGroup (↥H ⧸ N.subgroupOf H) := by
    rcases hX with hφ | ⟨hq, ⟨φ⟩⟩
    · obtain ⟨φ⟩ := hφ
      haveI := CFSG.RankThree.PartTwo.Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field
        (GaloisField 2 n)
      exact φ.isSimpleGroup
    · haveI := CFSG.RankThree.PartTwo.Sec4.Item462AltProof.isSimpleGroup_projSU_three 2 n
        (by omega) hq.ne'
      exact φ.isSimpleGroup
  have hH := hasOrderFourMod_of_quotient hNH hsimp
    (CFSG.RankThree.PartTwo.Sec15.exists_orderOf_eq_four_of_isLThreeEpsAt hX)
  set H' := H.map e.toMonoidHom with hH'
  have hH'4 : HasOrderFourMod H' := hH.map_equiv e
  have hperf' : ⁅H', H'⁆ = H' := by rw [hH', ← Subgroup.map_commutator, hperf]
  have hmemH' : ∀ h ∈ H, e h ∈ H' := fun h hh => Subgroup.mem_map_of_mem e.toMonoidHom hh
  have hfixH' : ∀ α : MulAut (CFSG.Assembly.RankThreeEven.projSL 3 K), (∀ h ∈ H, α h = h) →
      ∀ h ∈ H', MulAut.congr e α h = h := by
    intro α hα h hh
    obtain ⟨x, hx, rfl⟩ := hh
    rw [MulAut.congr_apply]
    change e (α (e.symm (e x))) = e x
    rw [MulEquiv.symm_apply_apply, hα x hx]
  refine ⟨fun U hU2 hHU => ?_, ?_, fun α β hα2 hβ2 hα1 hβ1 hαH hβH => ?_,
    fun β hβ2 hβ1 hβH => ?_⟩
  ·
    have hU' : U.map e.toMonoidHom = ⊥ := by
      refine eq_bot_of_isPGroup_of_le_normalizer hH'4 (hU2.map e.toMonoidHom) ?_
      rw [← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono hHU
    rw [eq_bot_iff]
    intro u hu
    have : e u ∈ U.map e.toMonoidHom := Subgroup.mem_map_of_mem e.toMonoidHom hu
    rw [hU', Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact (MulEquiv.map_eq_one_iff e).mp this
  ·
    have hC := centralizer_eq_bot hH'4 hperf'
    rw [eq_bot_iff]
    intro c hc
    have hc' : e c ∈ Subgroup.centralizer (H' : Set (projectiveSL 3 K)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨h, hh, rfl⟩
      have := Subgroup.mem_centralizer_iff.mp hc h hh
      change e h * e c = e c * e h
      rw [← map_mul, ← map_mul, this]
    rw [hC, Subgroup.mem_bot] at hc'
    rw [Subgroup.mem_bot]
    exact (MulEquiv.map_eq_one_iff e).mp hc'
  ·
    have h := eq_of_involution_of_fix hK (by omega) hH'4 hperf'
      (α := MulAut.congr e α) (β := MulAut.congr e β)
      (by rw [← map_pow, hα2, map_one]) (by rw [← map_pow, hβ2, map_one])
      (fun h1 => hα1 ((MulEquiv.map_eq_one_iff _).mp h1))
      (fun h1 => hβ1 ((MulEquiv.map_eq_one_iff _).mp h1)) (hfixH' α hαH) (hfixH' β hβH)
    exact (MulAut.congr e).injective h
  ·
    obtain ⟨j, hj⟩ := exists_comm_pow_twelve_ne_one hK hf4 hH'4 hperf'
      (β := MulAut.congr e β) (by rw [← map_pow, hβ2, map_one])
      (fun h1 => hβ1 ((MulEquiv.map_eq_one_iff _).mp h1)) (hfixH' β hβH)
    refine ⟨e.symm j, fun h => hj ?_⟩
    have h' := congrArg e h
    rw [map_one, map_pow, map_mul, map_inv, MulEquiv.apply_symm_apply] at h'
    rw [MulAut.congr_apply]
    exact h'

end CFSG.RankThree.PartTwo.Sec15.Ronan155DiamondL3
