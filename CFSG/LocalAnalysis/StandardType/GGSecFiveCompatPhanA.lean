module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanAMarked
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSADefs
public import CFSG.LocalAnalysis.StandardType.GGSelectedPSU
public import CFSG.LocalAnalysis.StandardType.GGCompatNbrSomeDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneConj
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSAPairAux

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan
  CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary

private theorem ggCompatPhanA_map_conj_map {A G : Type*} [Group A] [Group G] (θ : A →* G) (u : A)
    (Z : Subgroup A) :
    (Z.map (MulAut.conj u).toMonoidHom).map θ =
      (Z.map θ).map (MulAut.conj (θ u)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

private theorem ggCompatPhanA_map_symm_map {A B : Type*} [Group A] [Group B] (T : A ≃* B)
    (Z : Subgroup A) : (Z.map T.toMonoidHom).map T.symm.toMonoidHom = Z := by
  rw [Subgroup.map_map]
  have h : T.symm.toMonoidHom.comp T.toMonoidHom = MonoidHom.id A := by
    ext x
    simp
  rw [h, Subgroup.map_id]

theorem ggSecFiveCompatPhanA_of_marks
    (hNS : GGSecFiveNSKGPosAInput) (hL1 : GGSecFiveL1PhanInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hns : ¬ GGSplitLie p L)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) {m : ℕ} (σ : Fin m ≃ ι) (hm : 5 ≤ m)
    (hM : M = (CoxeterMatrix.A m).reindex σ)
    (hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6)
    {f : ℕ} (hf4 : 4 ≤ 2 ^ f)
    (θ : Su (GaloisField 2 (2 * f)) 2 f (m + 1) →* G)
    (hker : θ.ker ≤ Subgroup.center (Su (GaloisField 2 (2 * f)) 2 f (m + 1)))
    (hrange : θ.range = L ⊔ ⨆ K ∈ 𝒦, K) (hG0 : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K)
    (hmark : (ggSuPairBlock (GaloisField 2 (2 * f)) 2 f (m + 1) ⟨0, by omega⟩ ⟨1, by omega⟩).map θ =
      ggRankOnePerf Bs
        ((e (M.simple (σ ⟨0, by omega⟩)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs))
    (hP : ∃ ψs : (ggU .PSU (m + 1) f).K →* G,
      GGPresentsG0 (ggG0 p B x L D J) (ggU .PSU (m + 1) f).D .PSU (m + 1) f ψs) :
    ∃ ψ₀ : (ggU .PSU (m + 1) f).K →* G,
      GGPresentsG0 (ggG0 p B x L D J) (ggU .PSU (m + 1) f).D .PSU (m + 1) f ψ₀ ∧
        GGCompatPresented (ggU .PSU (m + 1) f).D ψ₀ L := by
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := by
    intro i j hij
    rw [hM, CoxeterMatrix.reindex_apply]
    simp only [CoxeterMatrix.A, Matrix.of_apply]
    split_ifs <;> omega
  haveI : Finite ι := ggIsWeylMatrix_finite hpres.1
  have hconn : GGSimplyLacedConnected M := ggSimplyLacedConnected_of_weyl hpres.1 hle3
  have hAH : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer (L ⊔ ⨆ K ∈ 𝒦, K) Bs :=
    ggAutomizerJoin_le_ggAutomizer L Bs 𝒦
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      norm_num at hf4
    · exact h
  have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf1
  obtain ⟨K_L, hKf, hKfin, hKchar, f_L, d, ψL, hKLcard, hd4, hkerL, hrangeL, hpL, hpos, -⟩ :=
    hNS G p B Bs x L D J 𝒦 hcfg hns ι M e hpres ⟨m, σ, hm, hM⟩ hbig L (Or.inl rfl) hns
  letI : Field K_L := hKf
  letI : Finite K_L := hKfin
  letI : CharP K_L 2 := hKchar
  have hf1L : 1 ≤ f_L := by
    rcases Nat.eq_zero_or_pos f_L with h | h
    · exfalso
      have h1 : 1 < Nat.card K_L := Finite.one_lt_card
      rw [hKLcard, h] at h1
      norm_num at h1
    · exact h
  unfold GGTableBPosSU at hpos
  obtain ⟨ε, hεrefl, hεlevi⟩ := hpos
  let a0 : Fin d := ⟨0, by omega⟩
  let b0 : Fin d := ⟨1, by omega⟩
  have hab : a0 ≠ b0 := by
    intro h
    have := congrArg Fin.val h
    simp [a0, b0] at this
  let r₀ : MulAut ↥Bs := ((ε (Equiv.swap a0 b0) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)
  have hr₀A : r₀ ∈ ggAutomizer L Bs := (ε (Equiv.swap a0 b0)).2
  have hr₀C : r₀ ∈ ggCoxRefl M e :=
    ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3
      (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hr₀A) (hεrefl a0 b0 hab)
  have hperf₀ : ggRankOnePerf Bs r₀ = ggRankOneIn L Bs r₀ :=
    hL1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 hbig L (Or.inl rfl) r₀ hr₀A hr₀C
  have hlevi : ggRankOneIn L Bs r₀ = (ggSuPairBlock K_L 2 f_L d a0 b0).map ψL :=
    hεlevi a0 b0 hab
  let k0 : Fin m := ⟨0, by omega⟩
  let r_k : MulAut ↥Bs := ((e (M.simple (σ k0)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)
  have hr_kC : r_k ∈ ggCoxRefl M e := by
    refine ⟨1, σ k0, ?_⟩
    change ((e (M.simple (σ k0)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
      ((e (1 * M.simple (σ k0) * 1⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)
    simp only [one_mul, inv_one, mul_one]
  obtain ⟨a, haA, hra⟩ := ggCoxRefl_conj_of_connected e hconn hr_kC hr₀C
  obtain ⟨g, hgH, -, hg⟩ := mem_ggAutomizer_iff.mp (hAH haA)
  rw [← hrange] at hgH
  obtain ⟨ũ, hũ⟩ := MonoidHom.mem_range.mp hgH
  obtain ⟨βN, γN, modelN, hblockN⟩ :=
    SelectedRoot.exists_selectedModel_PSU_block (F := GaloisField 2 (2 * f)) hF
      (by omega : 4 ≤ m + 1)
  have hFL : Nat.card (GaloisField 2 (2 * f_L)) = (2 ^ f_L) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 f_L hf1L
  obtain ⟨βd, γd, modeld, hblockd⟩ :=
    SelectedRoot.exists_selectedModel_PSU_block (F := GaloisField 2 (2 * f_L)) hFL hd4
  haveI : Fintype K_L := Fintype.ofFinite K_L
  haveI : Fintype (GaloisField 2 (2 * f_L)) := Fintype.ofFinite _
  let eL : K_L ≃+* GaloisField 2 (2 * f_L) := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hKLcard, hFL])
  have heL : ∀ c, eL (unitaryInvolution K_L 2 f_L c) =
      unitaryInvolution (GaloisField 2 (2 * f_L)) 2 f_L (eL c) := by
    intro c
    simp only [unitaryInvolution_apply, map_pow]
  let T : Su K_L 2 f_L d ≃* Su (GaloisField 2 (2 * f_L)) 2 f_L d := suidCongr eL heL d
  have hTblock : (ggSuPairBlock K_L 2 f_L d a0 b0).map T.toMonoidHom =
      ggSuPairBlock (GaloisField 2 (2 * f_L)) 2 f_L d a0 b0 :=
    SetLike.coe_injective (by
      simpa only [Subgroup.coe_map, MulEquiv.coe_toMonoidHom] using
        ggPhanNSAPairAux_suidCongr_pairBlock eL heL a0 b0)
  obtain ⟨ψ₀c, hψ₀c⟩ : ∃ ψ₀c : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1) →* G,
      ψ₀c = θ.comp βN.toMonoidHom := ⟨_, rfl⟩
  obtain ⟨ψ'c, hψ'c⟩ : ∃ ψ'c : SU (unitaryInvolution (GaloisField 2 (2 * f_L)) 2 f_L) d →* G,
      ψ'c = ψL.comp (T.symm.toMonoidHom.comp βd.toMonoidHom) := ⟨_, rfl⟩
  have hker₀ : ψ₀c.ker ≤ Subgroup.center
      (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1)) := by
    rw [hψ₀c, ← MonoidHom.comap_ker]
    exact le_trans (Subgroup.comap_mono hker)
      (Subgroup.comap_center_le_center (f := βN.toMonoidHom) βN.injective)
  have hker' : ψ'c.ker ≤ Subgroup.center
      (SU (unitaryInvolution (GaloisField 2 (2 * f_L)) 2 f_L) d) := by
    rw [hψ'c, ← MonoidHom.comap_ker]
    exact le_trans (Subgroup.comap_mono hkerL)
      (Subgroup.comap_center_le_center (f := T.symm.toMonoidHom.comp βd.toMonoidHom)
        (T.symm.injective.comp βd.injective))
  have hrange₀ : ψ₀c.range = ggG0 p B x L D J := by
    rw [hψ₀c, MonoidHom.range_comp,
      (MonoidHom.range_eq_top (f := βN.toMonoidHom)).mpr βN.surjective, Subgroup.map_top,
      hrange, hG0]
  have hrange' : ψ'c.range = L := by
    rw [hψ'c, MonoidHom.range_comp, MonoidHom.range_comp,
      (MonoidHom.range_eq_top (f := βd.toMonoidHom)).mpr βd.surjective, Subgroup.map_top,
      (MonoidHom.range_eq_top (f := T.symm.toMonoidHom)).mpr T.symm.surjective, Subgroup.map_top,
      hrangeL]
  let u₀ : SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 1) := βN.symm ũ
  have hLHS : ((ψ₀c.comp (MulAut.conj u₀).toMonoidHom).comp modelN.phi).range =
      ggRankOnePerf Bs r₀ := by
    have hβu : βN u₀ = ũ := MulEquiv.apply_symm_apply βN ũ
    calc ((ψ₀c.comp (MulAut.conj u₀).toMonoidHom).comp modelN.phi).range
        = (modelN.phi.range.map (MulAut.conj u₀).toMonoidHom).map ψ₀c := by
          rw [MonoidHom.range_comp, ← Subgroup.map_map]
      _ = ((modelN.phi.range.map (MulAut.conj u₀).toMonoidHom).map βN.toMonoidHom).map θ := by
          rw [hψ₀c, ← Subgroup.map_map]
      _ = ((modelN.phi.range.map βN.toMonoidHom).map (MulAut.conj ũ).toMonoidHom).map θ := by
          rw [ggCompatPhanA_map_conj_map βN.toMonoidHom u₀, MulEquiv.coe_toMonoidHom, hβu]
      _ = ((ggSuPairBlock (GaloisField 2 (2 * f)) 2 f (m + 1) ⟨0, by omega⟩
            ⟨1, by omega⟩).map (MulAut.conj ũ).toMonoidHom).map θ := by rw [hblockN]
      _ = ((ggSuPairBlock (GaloisField 2 (2 * f)) 2 f (m + 1) ⟨0, by omega⟩
            ⟨1, by omega⟩).map θ).map (MulAut.conj (θ ũ)).toMonoidHom :=
          ggCompatPhanA_map_conj_map θ ũ _
      _ = (ggRankOnePerf Bs r_k).map (MulAut.conj g).toMonoidHom := by rw [hmark, hũ]
      _ = ggRankOnePerf Bs (a * r_k * a⁻¹) := ggRankOnePerf_map_conj hg r_k
      _ = ggRankOnePerf Bs r₀ := by rw [← hra]
  have hRHS : (ψ'c.comp modeld.phi).range = ggRankOnePerf Bs r₀ := by
    calc (ψ'c.comp modeld.phi).range
        = ((modeld.phi.range.map βd.toMonoidHom).map T.symm.toMonoidHom).map ψL := by
          rw [hψ'c, MonoidHom.range_comp, ← Subgroup.map_map, ← Subgroup.map_map]
      _ = ((ggSuPairBlock (GaloisField 2 (2 * f_L)) 2 f_L d a0 b0).map
            T.symm.toMonoidHom).map ψL := by rw [hblockd]
      _ = (ggSuPairBlock K_L 2 f_L d a0 b0).map ψL := by
          rw [← hTblock, ggCompatPhanA_map_symm_map T]
      _ = ggRankOneIn L Bs r₀ := hlevi.symm
      _ = ggRankOnePerf Bs r₀ := hperf₀.symm
  obtain ⟨u, hmatch⟩ :=
    SelectedRoot.selectedRootMatch_of_map_eq modelN modeld ψ₀c ψ'c hker₀ hker' u₀
      (hLHS.trans hRHS.symm)
  have hD : ∀ (n f' : ℕ) (hf' : 1 ≤ f'), ggU .PSU n f' =
      ⟨Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f')) 2 f') n,
        Unitary.rootDatum (CFSG.LieType.Universal.card_galoisField_two_mul 2 f' hf') n⟩ :=
    fun n f' hf' => by simp only [ggU, lieUniversal, hf', ↓reduceDIte]
  have hadm₀ : StatedLieAdmissible .PSU (m + 1) 2 f :=
    ⟨Nat.prime_two, hf1, by omega, fun h => by
      have := congrArg Prod.fst h
      simp only at this
      omega⟩
  have hadm' : StatedLieAdmissible .PSU d 2 f_L :=
    ⟨Nat.prime_two, hf1L, by omega, fun h => by
      have := congrArg Prod.fst h
      simp only at this
      omega⟩
  obtain ⟨ψs, ⟨-, -⟩, -, hperf, hmodel⟩ := hP
  rw [hD (m + 1) f hf1]
  refine ⟨ψ₀c, ⟨⟨hadm₀, ?_⟩, ⟨hrange₀, hker₀⟩, hperf, hmodel⟩, ?_⟩
  · show 2 ≤ (m + 1) / 2
    omega
  · refine ⟨.PSU, d, f_L, ?_⟩
    rw [hD d f_L hf1L]
    refine ⟨ψ'c, hadm', ?_, hker', hrange', γd, modeld.root_mem, γN, modelN.root_mem, u, hmatch⟩
    show 2 ≤ d / 2
    omega

end CFSG.StandardType

end
