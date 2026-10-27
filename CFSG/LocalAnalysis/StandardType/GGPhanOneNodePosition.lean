module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatJoinCells
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
public import CFSG.LocalAnalysis.StandardType.PhanEStdRootNodes

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.Assembly.LowTwoRank

theorem exists_conj_node_eq_ggRankOnePerf {G : Type} [Group G] [Finite G]
    {Y : Type*} [Group Y] (ψ : Y →* G) {H Bs : Subgroup G}
    (hrange : ψ.range = H) {A : Subgroup (MulAut ↥Bs)} {ι : Type}
    {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A) (hM : GGSimplyLacedConnected M)
    (hA : A ≤ ggAutomizer H Bs) {r₀ : MulAut ↥Bs} (hr₀ : r₀ ∈ ggCoxRefl M e)
    (i : ι) (N : Subgroup Y)
    (hN : N.map ψ = ggRankOnePerf Bs ((e (M.simple i) : ↥A) : MulAut ↥Bs)) :
    ∃ u : Y, (N.map (MulAut.conj u).toMonoidHom).map ψ = ggRankOnePerf Bs r₀ := by
  obtain ⟨a, ha, hai⟩ := ggSimple_eq_conj_of_mem_ggCoxRefl e hM hr₀ i
  obtain ⟨g, hg, -, hmap⟩ := exists_ggRankOnePerf_conj_of_mem_ggAutomizer (hA ha) r₀
  have hback : (ggRankOnePerf Bs ((e (M.simple i) : ↥A) : MulAut ↥Bs)).map
      (MulAut.conj g⁻¹).toMonoidHom = ggRankOnePerf Bs r₀ := by
    rw [hai, ← hmap, Subgroup.map_map]
    have hid : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hid, Subgroup.map_id]
  have hginv : g⁻¹ ∈ ψ.range := by rw [hrange]; exact H.inv_mem hg
  obtain ⟨u, hu⟩ := hginv
  refine ⟨u, ?_⟩
  rw [Subgroup.map_map_conj, hu, hN]
  exact hback


open PsiDiag PsiDiagChar RankOneXfer in
theorem ggSecFiveCompat_of_phan_node {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ)
    {A : Subgroup (MulAut ↥Bs)} {ι : Type} {M : CoxeterMatrix ι}
    (e : M.Group ≃* ↥A) (hM : GGSimplyLacedConnected M)
    (hA : A ≤ ggAutomizer (ggG0 p B x L D J) Bs)
    {r₀ : MulAut ↥Bs} (hr₀ : r₀ ∈ ggCoxRefl M e) (i : ι)
    (N : Subgroup (ggU t n f).K)
    (hN : N.map ψ = ggRankOnePerf Bs ((e (M.simple i) : ↥A) : MulAut ↥Bs))
    {K : Subgroup G} (hK : K = L ∨ ∃ y : G, GGNbr p B x D J y K)
    {t' : StatedLieTag} {n' f' : ℕ} {ψ' : (ggU t' n' f').K →* G}
    (hadm : StatedLieAdmissible t' n' 2 f') (hrk : 2 ≤ (ggU t' n' f').D.rank)
    (hker' : ψ'.ker ≤ Subgroup.center (ggU t' n' f').K) (hrange' : ψ'.range = K)
    {k k' : Type*} [Field k] [Finite k] [CharP k 2] [Field k'] [Finite k'] [CharP k' 2]
    {γ : Fin (ggU t n f).D.rank → ℤ} {δ : Fin (ggU t' n' f').D.rank → ℤ}
    (phi : Matrix.SpecialLinearGroup (Fin 2) k →* (ggU t n f).K)
    (hphi : Function.Injective phi) (hγ : γ ∈ (ggU t n f).D.roots)
    (hupper : (sl2UpperUniSub k).map phi = (ggU t n f).D.rootGroup γ)
    (hdiag : ∀ a : kˣ, phi (sl2Diag a) ∈ ggTorus (ggU t n f).D)
    (v : (ggU t n f).K) (hphiN : phi.range.map (MulAut.conj v).toMonoidHom = N)
    (model' : SelectedRoot.SelectedSL2Model (ggU t' n' f').D k' δ)
    (hmember : (ψ'.comp model'.phi).range = ggRankOnePerf Bs r₀) :
    GGSecFiveCompat p B x L D J := by
  obtain ⟨u, hu⟩ := exists_conj_node_eq_ggRankOnePerf ψ hpres.2.1.1 e hM hA hr₀ i N hN
  apply ggSecFiveCompat_of_sl2Embedding hpres hK hadm hrk hker' hrange'
    phi hphi hγ hupper hdiag model' (u * v)
  rw [hmember, MonoidHom.range_comp, ← Subgroup.map_map]
  have hconj : (MulAut.conj (u * v)).toMonoidHom =
      (MulAut.conj u).toMonoidHom.comp (MulAut.conj v).toMonoidHom := by
    ext y
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [hconj, ← Subgroup.map_map, hphiN]
  exact hu


open CFSG.ClassicalInvolution.Phan.PhanE CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.RootSystem PsiDiagChar RankOneXfer in
theorem ggSecFiveCompat_of_e7_stdConfig_node {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {n f : ℕ} {ψ : (ggU .E7 n f).K →* G}
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU .E7 n f).D .E7 n f ψ)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    {A : Subgroup (MulAut ↥Bs)} {ι : Type} {M : CoxeterMatrix ι}
    (e : M.Group ≃* ↥A) (hM : GGSimplyLacedConnected M)
    (hA : A ≤ ggAutomizer (ggG0 p B x L D J) Bs)
    {r₀ : MulAut ↥Bs} (hr₀ : r₀ ∈ ggCoxRefl M e) (i : ι)
    (j : Fin (CFSG.Blueprint.Chevalley.Tag.rank .E7))
    (hN : (((e7StdConfig F f hF (one_le_of_four_le_two_pow hq)).S.ι j).range).map ψ =
      ggRankOnePerf Bs ((e (M.simple i) : ↥A) : MulAut ↥Bs))
    {K : Subgroup G} (hK : K = L ∨ ∃ y : G, GGNbr p B x D J y K)
    {t' : StatedLieTag} {n' f' : ℕ} {ψ' : (ggU t' n' f').K →* G}
    (hadm : StatedLieAdmissible t' n' 2 f') (hrk : 2 ≤ (ggU t' n' f').D.rank)
    (hker' : ψ'.ker ≤ Subgroup.center (ggU t' n' f').K) (hrange' : ψ'.range = K)
    {k' : Type*} [Field k'] [Finite k'] [CharP k' 2]
    {δ : Fin (ggU t' n' f').D.rank → ℤ}
    (model' : SelectedRoot.SelectedSL2Model (ggU t' n' f').D k' δ)
    (hmember : (ψ'.comp model'.phi).range = ggRankOnePerf Bs r₀) :
    GGSecFiveCompat p B x L D J := by
  obtain ⟨φ, hφ, hupper, hdiag, v, hv⟩ := exists_e7_stdConfig_primitive_node
    (n := n) hF (one_le_of_four_le_two_pow hq) j
  have hroot : (Pi.single j 1 : Fin (ggU .E7 n f).D.rank → ℤ) ∈
      (ggU .E7 n f).D.roots :=
    (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 (GaloisField 2 f)).2
      (CFSG.Blueprint.Chevalley.isRoot_single .E7 j)
  exact ggSecFiveCompat_of_phan_node hpres e hM hA hr₀ i
    (((e7StdConfig F f hF (one_le_of_four_le_two_pow hq)).S.ι j).range)
    hN hK hadm hrk hker' hrange' φ hφ hroot hupper hdiag v hv model' hmember

end CFSG.StandardType
