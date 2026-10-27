module

public import CFSG.LocalAnalysis.StandardType.GGExcKGInndiagCIE6
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeFrameOn
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagE6Toral
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (IsElemAbelian)
open TableBExc.E6Three

private theorem e6t_map_conj_map_conj {A : Type*} [Group A] (S : Subgroup A) (a b : A) :
    (S.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      S.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
  group

private theorem e6t_map_conj_one {A : Type*} [Group A] (S : Subgroup A) :
    S.map (MulAut.conj (1 : A)).toMonoidHom = S := by
  have h : (MulAut.conj (1 : A)).toMonoidHom = MonoidHom.id A := by
    ext x
    simp [MulAut.conj_apply]
  rw [h, Subgroup.map_id]

private theorem e6t_fixCard_one {p : ℕ} (hp : p.Prime) (R : ℕ) :
    GGFixCard p (1 : Equiv.Perm (Fin R)) = p ^ R := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  unfold GGFixCard
  have h : Nat.card {z : Fin R → ZMod p // ∀ i, z ((1 : Equiv.Perm (Fin R)) i) = z i} =
      Nat.card (Fin R → ZMod p) :=
    Nat.card_congr (Equiv.subtypeUnivEquiv fun z i => rfl)
  rw [h, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem e6t_mem_normalizer
    {n f : ℕ} (hN : ((ggPsiU .E6 n f).range).Normal)
    (c : GGAutU .E6 n f) :
    c ∈ Subgroup.normalizer ((ggPsiU .E6 n f).range : Set (GGAutU .E6 n f)) := by
  refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => hN.conj_mem h hh c, fun hh => ?_⟩
  have := hN.conj_mem _ hh c⁻¹
  simpa [mul_assoc] using this

private theorem e6t_bridge
    {n f : ℕ} (hadm : GGKnownAdm .E6 n f) :
    ∃ Φ : GGAutU .E6 n f →* MulAut (adjointGroup .E6 (GaloisField 2 f)),
      Function.Injective Φ ∧
      (∀ b, GGInnDiagU .E6 n f b → Φ b ∈ (hatAut .E6 (GaloisField 2 f)).range) ∧
      (∀ c : adjointGroup .E6 (GaloisField 2 f),
        ∃ κ ∈ (ggPsiU .E6 n f).range, Φ κ = MulAut.conj c) := by
  haveI : Finite (ggU .E6 n f).K := ggU_finite_exc (Or.inr (Or.inl rfl)) hadm
  haveI : Finite (GGAutU .E6 n f) := GGSFCore.finite_ggAutU
  haveI hN : ((ggPsiU .E6 n f).range).Normal := GGSFCore.normal_range_ggPsiU .E6 n f
  obtain ⟨-, hker, -, hcent⟩ := ggKnownSetting_autU hadm
  obtain ⟨χ, hχinj, hχrange, hval⟩ :=
    NoOffE6Three.exists_injective_factor_E6_comp (ggPsiU .E6 n f) hker hcent
  have hM : (⊤ : Subgroup (GGAutU .E6 n f)) ≤
      Subgroup.normalizer (χ.range : Set (GGAutU .E6 n f)) := by
    rw [hχrange]
    intro g _
    exact e6t_mem_normalizer hN g
  have hCχ : Subgroup.centralizer (χ.range : Set (GGAutU .E6 n f)) = ⊥ := by
    rw [hχrange]
    exact hcent
  let Φ : GGAutU .E6 n f →* MulAut (adjointGroup .E6 (GaloisField 2 f)) :=
    (NormalizerAut.normAutOn χ hχinj hM).comp
      (Subgroup.topEquiv (G := GGAutU .E6 n f)).symm.toMonoidHom
  have hΦ : ∀ b, Φ b = NormalizerAut.normAutOn χ hχinj hM ⟨b, Subgroup.mem_top b⟩ :=
    fun b => rfl
  refine ⟨Φ, ?_, ?_, ?_⟩
  · exact (NormalizerAut.normAutOn_injective χ hχinj hM hCχ).comp
      (Subgroup.topEquiv (G := GGAutU .E6 n f)).symm.injective
  · intro b hb
    have hbN : b ∈ Subgroup.normalizer ((ggPsiU .E6 n f).range : Set (GGAutU .E6 n f)) :=
      e6t_mem_normalizer hN b
    obtain ⟨α, hαD, hα⟩ := LayerSixE.exists_induces_E6 (ggPsiU .E6 n f) hker hbN hb
    have hind := NormalizerAut.ggInduces_normAutOn (π := e6Isogeny (GaloisField 2 f))
      (ψ := ggPsiU .E6 n f) χ hχinj hval hM ⟨b, Subgroup.mem_top b⟩
    have huniq := LayerSixE.GGInduces.unique (e6Isogeny_surjective (GaloisField 2 f)) hbN hind hα
    rw [hΦ, huniq, NoOffE6Three.hatAut_range_eq_sup]
    exact hαD
  · intro c
    refine ⟨χ c, ?_, ?_⟩
    · rw [← hχrange]
      exact ⟨c, rfl⟩
    · rw [hΦ]
      exact NormalizerAut.normAutOn_chi χ hχinj hM c (Subgroup.mem_top _)

theorem ggKGInndiagCIa_E6_three
    (n f : ℕ) (hadm : GGKnownAdm .E6 n f)
    {π : Equiv.Perm (Fin (ggU (absTag .E6) 6 f).D.rank)} (hπ : π = 1) (h3 : 3 ∣ 2 ^ f - 1)
    {E : Subgroup (GGAutU .E6 n f)} (hE : IsElemAbelian 3 E)
    (hdiag : ∀ b ∈ E, GGInnDiagU .E6 n f b) : Nat.card E ≤ GGFixCard 3 π := by
  subst hπ
  obtain ⟨Φ, hΦinj, hΦdiag, -⟩ := e6t_bridge hadm
  have hf : f ≠ 0 := by have := hadm.1.2.1; omega
  have h3K : 3 ∣ Nat.card (GaloisField 2 f) - 1 := by
    rw [GaloisField.card 2 f hf]
    exact h3
  have hXI : E.map Φ ≤ (hatAut .E6 (GaloisField 2 f)).range := by
    rintro _ ⟨b, hb, rfl⟩
    exact hΦdiag b (hdiag b hb)
  have hbound := (card_le_and_normalizes_of_le_hatAut h3K (IsElemAbelian.map hE Φ) hXI).1
  rw [Subgroup.card_map_of_injective hΦinj] at hbound
  rw [e6t_fixCard_one Nat.prime_three]
  exact hbound

theorem ggKGInndiagCId_E6_three
    (n f : ℕ) (hadm : GGKnownAdm .E6 n f)
    {π : Equiv.Perm (Fin (ggU (absTag .E6) 6 f).D.rank)} (hπ : π = 1) (h3 : 3 ∣ 2 ^ f - 1)
    {E E' : Subgroup (GGAutU .E6 n f)} (hE : IsElemAbelian 3 E) (hE' : IsElemAbelian 3 E')
    (hdiag : ∀ b ∈ E, GGInnDiagU .E6 n f b) (hdiag' : ∀ b ∈ E', GGInnDiagU .E6 n f b)
    (hcE : Nat.card E = GGFixCard 3 π) (hcE' : Nat.card E' = GGFixCard 3 π) :
    ∃ κ : GGAutU .E6 n f, GGInnDiagU .E6 n f κ ∧
      E.map (MulAut.conj κ).toMonoidHom = E' := by
  subst hπ
  obtain ⟨Φ, hΦinj, hΦdiag, hΦinn⟩ := e6t_bridge hadm
  have hf : f ≠ 0 := by have := hadm.1.2.1; omega
  have h3K : 3 ∣ Nat.card (GaloisField 2 f) - 1 := by
    rw [GaloisField.card 2 f hf]
    exact h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := GaloisField 2 f) h3K
  have hζ : ζ ^ 3 = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  rw [e6t_fixCard_one Nat.prime_three] at hcE hcE'
  have key : ∀ F : Subgroup (GGAutU .E6 n f), IsElemAbelian 3 F →
      (∀ b ∈ F, GGInnDiagU .E6 n f b) → Nat.card F = 3 ^ 6 →
      ∃ g : adjointGroup .E6 (GaloisField 2 f),
        (F.map Φ).map (MulAut.conj (MulAut.conj g)).toMonoidHom = NoOffE6Three.vAd ζ hζ := by
    intro F hF hFd hFc
    have hXI : F.map Φ ≤ (hatAut .E6 (GaloisField 2 f)).range := by
      rintro _ ⟨b, hb, rfl⟩
      exact hΦdiag b (hFd b hb)
    have h6 : 3 ^ 6 ≤ Nat.card (F.map Φ) := by
      rw [Subgroup.card_map_of_injective hΦinj, hFc]
    obtain ⟨γ, hγ, hγeq⟩ :=
      NoOffE6Three.exists_conj_eq_vAd h3K hζo hζ (IsElemAbelian.map hF Φ) hXI h6
    obtain ⟨g, hg⟩ :=
      OutdiagE6.exists_inner_conj_map_le (OutdiagE6.vAd_le_diag ζ hζ) hγ hγeq.le
    refine ⟨g, Subgroup.eq_of_le_of_card_ge hg ?_⟩
    rw [Subgroup.card_map_of_injective (MulAut.conj (MulAut.conj g)).injective,
      NoOffE6Three.card_vAd hζo hζ]
    exact h6
  obtain ⟨g, hg⟩ := key E hE hdiag hcE
  obtain ⟨g', hg'⟩ := key E' hE' hdiag' hcE'
  obtain ⟨κ, hκr, hκ⟩ := hΦinn (g'⁻¹ * g)
  refine ⟨κ, GGSFCore.ggInnDiagU_of_mem_range hκr, ?_⟩
  apply Subgroup.map_injective hΦinj
  have h1 : (E.map (MulAut.conj κ).toMonoidHom).map Φ =
      (E.map Φ).map (MulAut.conj (Φ κ)).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, map_mul, map_inv]
  have e1 : MulAut.conj (g'⁻¹ * g) = (MulAut.conj g')⁻¹ * MulAut.conj g := by
    rw [map_mul, map_inv]
  rw [h1, hκ, e1, ← e6t_map_conj_map_conj (E.map Φ), hg, ← hg', e6t_map_conj_map_conj,
    inv_mul_cancel, e6t_map_conj_one]

end CFSG.StandardType
