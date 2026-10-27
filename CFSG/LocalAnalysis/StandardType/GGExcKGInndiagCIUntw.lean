module

public import CFSG.LocalAnalysis.StandardType.GGExcKGSFCore
public import CFSG.LocalAnalysis.StandardType.GGExcKGSFFinite
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRest
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerAdj
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerE7
public import CFSG.LocalAnalysis.StandardType.GGExcFieldRankE7
public import CFSG.LocalAnalysis.StandardType.GGExcFieldRankE8
public import CFSG.LocalAnalysis.StandardType.GGExcFieldAutCentRankF4Rank
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
public import CFSG.LieType.Steinberg.Isogeny.E7
public import Certificates.Certificate45
public import Certificates.Certificate49
public import Certificates.Certificate53
public import Certificates.Certificate59
public import Certificates.Certificate68
public import Certificates.Certificate72
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.CentralExt CFSG.LieType.Steinberg.CentralExt.FieldFour
  CFSG.LieType.Steinberg.CentralExt.MinusculeClosed CFSG.LieType.SeitzGeneration
open CFSG.Open (IsElemAbelian)

private theorem ciaMap {K A : Type*} [Group K] [Group A] (Φ : K →* A)
    (hΦ : Function.Injective Φ) {p : ℕ} {E : Subgroup K} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.map Φ) ∧ Nat.card (E.map Φ) = Nat.card E := by
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, Subgroup.card_map_of_injective hΦ⟩
  · obtain ⟨_, a, ha, rfl⟩ := a
    obtain ⟨_, b, hb, rfl⟩ := b
    apply Subtype.ext
    have h : a * b = b * a := congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    show Φ a * Φ b = Φ b * Φ a
    rw [← map_mul, ← map_mul, h]
  · obtain ⟨y, hy, rfl⟩ := hx
    rw [← map_pow, hE.2 y hy, map_one]

private theorem ciaComap {K G : Type*} [Group K] [Group G] (ψ : K →* G)
    (hinj : Function.Injective ψ) {p : ℕ} {E : Subgroup G} (hEr : E ≤ ψ.range)
    (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.comap ψ) ∧ Nat.card (E.comap ψ) = Nat.card E := by
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · apply Subtype.ext; apply hinj
    have h := congrArg Subtype.val (hE.1.is_comm.comm ⟨ψ a, a.2⟩ ⟨ψ b, b.2⟩)
    simpa [map_mul] using h
  · apply hinj; rw [map_pow, map_one]; exact hE.2 _ hx
  · have h1 := Nat.card_congr (Subgroup.equivMapOfInjective (E.comap ψ) ψ hinj).toEquiv
    rw [Subgroup.map_comap_eq_self hEr] at h1
    exact h1

private theorem ciaDvdSq {f p : ℕ} (hreg : GGExcRegime p f) : p ∣ (2 ^ f) ^ 2 - 1 := by
  have ha : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have h1 : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
    have : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [ha, this]; ring
  rw [h1]
  rcases hreg with h | h
  · exact h.mul_right _
  · exact h.mul_left _

private theorem ciaOrder_dvd_two {p q : ℕ} (hq : 0 < q) (h : p ∣ q ^ 2 - 1) :
    orderOf ((q : ℕ) : ZMod p) ∣ 2 := by
  have h0 : (((q ^ 2 - 1 : ℕ)) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).2 h
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow, Nat.cast_one, sub_eq_zero] at h0
  exact orderOf_dvd_of_pow_eq_one h0

private theorem ciaFixCard_one {p : ℕ} (hp : p.Prime) (R : ℕ) :
    GGFixCard p (1 : Equiv.Perm (Fin R)) = p ^ R := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  unfold GGFixCard
  have h : Nat.card {z : Fin R → ZMod p // ∀ i, z ((1 : Equiv.Perm (Fin R)) i) = z i} =
      Nat.card (Fin R → ZMod p) :=
    Nat.card_congr (Equiv.subtypeUnivEquiv fun z i => rfl)
  rw [h, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem ciaBound_F4
    {f : ℕ} (hf : f ≠ 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hreg : GGExcRegime p f) {E : Subgroup (adjointGroup .F4 (GaloisField 2 f))}
    (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ 4 := by
  have hq : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf
  exact ExcFieldAutCentRankF4.card_le_pow_four hp hp2 (by rw [hq]; exact ciaDvdSq hreg) hE

private theorem ciaBound_E7
    {f : ℕ} (hf : f ≠ 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hreg : GGExcRegime p f) {E : Subgroup (adjointGroup .E7 (GaloisField 2 f))}
    (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ 7 := by
  have hq : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf
  have hdvd : orderOf ((Nat.card (GaloisField 2 f) : ℕ) : ZMod p) ∣ 2 := by
    rw [hq]; exact ciaOrder_dvd_two (by positivity) (ciaDvdSq hreg)
  have h7 : degCount .E7 (orderOf ((Nat.card (GaloisField 2 f) : ℕ) : ZMod p)) = 7 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h <;> rw [h] <;> decide
  have key := rankLE_E7 (K := GaloisField 2 f) hp hp2 rfl E hE
  rwa [h7] at key

private theorem ciaBound_E8
    {f : ℕ} (hf : f ≠ 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hreg : GGExcRegime p f) {E : Subgroup (adjointGroup .E8 (GaloisField 2 f))}
    (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ 8 := by
  have hq : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf
  have hdvd : orderOf ((Nat.card (GaloisField 2 f) : ℕ) : ZMod p) ∣ 2 := by
    rw [hq]; exact ciaOrder_dvd_two (by positivity) (ciaDvdSq hreg)
  have h8 : degCount .E8 (orderOf ((Nat.card (GaloisField 2 f) : ℕ) : ZMod p)) = 8 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h <;> rw [h] <;> decide
  have key := rankLE_E8 (K := GaloisField 2 f) hp hp2 rfl E hE
  rwa [h8] at key

theorem ggKnownSetting_autU
    {t : StatedLieTag} {n f : ℕ} (hadm : GGKnownAdm t n f) :
    GGKnownSetting t n f (ggPsiU t n f) := by
  obtain ⟨hadm', hrk⟩ := hadm
  obtain ⟨hcomm, -⟩ := ggU_perfect_lieModel hadm' hrk
  haveI hperf : Group.IsPerfect (ggU t n f).K := Group.isPerfect_def.mpr hcomm
  have hZ : Subgroup.center ((ggU t n f).K ⧸ Subgroup.center (ggU t n f).K) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot _
  have hker : (ggPsiU t n f).ker ≤ Subgroup.center (ggU t n f).K := by
    intro k hk
    have h1 : (QuotientGroup.mk k : (ggU t n f).K ⧸ Subgroup.center (ggU t n f).K) ∈
        Subgroup.center ((ggU t n f).K ⧸ Subgroup.center (ggU t n f).K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h2 := DFunLike.congr_fun (MonoidHom.mem_ker.1 hk) y
      simp only [ggPsiU, MonoidHom.comp_apply, QuotientGroup.mk'_apply, MulAut.conj_apply,
        MulAut.one_apply] at h2
      exact (mul_inv_eq_iff_eq_mul.1 h2).symm
    rw [hZ, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff k).1 h1
  refine ⟨⟨hadm', hrk⟩, hker, ⟨?_, lieModel_range_centerQuot hadm' hrk (ggPsiU t n f) hker⟩, ?_⟩
  · haveI := Group.IsPerfect.range (ggPsiU t n f)
    exact Group.IsPerfect.commutator_eq_top
  · rw [eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_bot]
    ext y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
    have hc := Subgroup.mem_centralizer_iff.1 hσ (ggPsiU t n f k) ⟨k, rfl⟩
    have key : ∀ z : (ggU t n f).K ⧸ Subgroup.center (ggU t n f).K,
        (QuotientGroup.mk k) * z * (QuotientGroup.mk k)⁻¹ =
          σ (QuotientGroup.mk k) * z * (σ (QuotientGroup.mk k))⁻¹ := by
      intro z
      have h2 := DFunLike.congr_fun hc (σ.symm z)
      simp only [ggPsiU, MonoidHom.comp_apply, QuotientGroup.mk'_apply, MulAut.mul_apply,
        MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply] at h2
      exact h2
    have hcen : (σ (QuotientGroup.mk k))⁻¹ * QuotientGroup.mk k ∈
        Subgroup.center ((ggU t n f).K ⧸ Subgroup.center (ggU t n f).K) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h3 : ((σ (QuotientGroup.mk k))⁻¹ * QuotientGroup.mk k) * z *
          ((σ (QuotientGroup.mk k))⁻¹ * QuotientGroup.mk k)⁻¹ = z := by
        calc _ = (σ (QuotientGroup.mk k))⁻¹ * ((QuotientGroup.mk k) * z *
              (QuotientGroup.mk k)⁻¹) * σ (QuotientGroup.mk k) := by group
          _ = z := by rw [key z]; group
      exact (mul_inv_eq_iff_eq_mul.1 h3).symm
    rw [hZ, Subgroup.mem_bot] at hcen
    exact inv_mul_eq_one.1 hcen

theorem ggInnDiagU_mem_range_of_untwisted
    {t : StatedLieTag}
    (ht : t = .F4 ∨ t = .E7 ∨ t = .E8) {n f : ℕ} (hadm : GGKnownAdm t n f)
    {c : GGAutU t n f} (hc : GGInnDiagU t n f c) : c ∈ (ggPsiU t n f).range := by
  have hexc : GGExcFive t := by
    rcases ht with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  haveI : Finite (ggU t n f).K := ggU_finite_exc hexc hadm
  haveI : Finite (GGAutU t n f) := GGSFCore.finite_ggAutU
  haveI hN : ((ggPsiU t n f).range).Normal := GGSFCore.normal_range_ggPsiU t n f
  obtain ⟨⟨hadm', hrk⟩, hker, ⟨hcomm, hlie⟩, hcent⟩ := ggKnownSetting_autU hadm
  have hpres : GGPresentsG0 (ggPsiU t n f).range (ggU t n f).D t n f (ggPsiU t n f) :=
    ⟨⟨hadm', hrk⟩, ⟨rfl, hker⟩, hcomm, hlie⟩
  have hnorm : c ∈ Subgroup.normalizer ((ggPsiU t n f).range : Set (GGAutU t n f)) := by
    refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => hN.conj_mem h hh c, fun hh => ?_⟩
    have := hN.conj_mem _ hh c⁻¹
    simpa [mul_assoc] using this
  obtain ⟨g, hg, hcg⟩ : ∃ g ∈ (ggPsiU t n f).range,
      c * g ∈ Subgroup.centralizer ((ggPsiU t n f).range : Set (GGAutU t n f)) := by
    rcases ht with rfl | rfl | rfl
    · exact ggPsiDiagInner_F4 (GGAutU .F4 n f) n f (ggPsiU .F4 n f) _ hpres c hnorm hc
    · exact ggPsiDiagInner_E7 (GGAutU .E7 n f) n f (ggPsiU .E7 n f) _ hpres c hnorm hc
    · exact ggPsiDiagInner_E8 (GGAutU .E8 n f) n f (ggPsiU .E8 n f) _ hpres c hnorm hc
  rw [hcent, Subgroup.mem_bot] at hcg
  rw [eq_inv_of_mul_eq_one_left hcg]
  exact (ggPsiU t n f).range.inv_mem hg

theorem ggKGInndiagCIa_F4
    (n f : ℕ) (hadm : GGKnownAdm .F4 n f) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hreg : GGExcRegime p f) {E : Subgroup (GGAutU .F4 n f)}
    (hE : IsElemAbelian p E) (hdiag : ∀ b ∈ E, GGInnDiagU .F4 n f b) : Nat.card E ≤ p ^ 4 := by
  have hf : f ≠ 0 := by have := hadm.1.2.1; omega
  have hset := ggKnownSetting_autU hadm
  have hEr : E ≤ (ggPsiU .F4 n f).range := fun b hb =>
    ggInnDiagU_mem_range_of_untwisted (Or.inl rfl) hadm (hdiag b hb)
  have hinj : Function.Injective (ggPsiU .F4 n f) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hset.2.1.trans (center_adjointGroup_eq_bot (τ := .F4) (K := GaloisField 2 f)).le
  obtain ⟨hE', hcard⟩ := ciaComap (ggPsiU .F4 n f) hinj hEr hE
  exact hcard.symm.le.trans (ciaBound_F4 hf hp hp2 hreg
    (E := (E.comap (ggPsiU .F4 n f) : Subgroup ↥(adjointGroup .F4 (GaloisField 2 f)))) hE')

theorem ggKGInndiagCIa_E7
    (n f : ℕ) (hadm : GGKnownAdm .E7 n f) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hreg : GGExcRegime p f) {E : Subgroup (GGAutU .E7 n f)}
    (hE : IsElemAbelian p E) (hdiag : ∀ b ∈ E, GGInnDiagU .E7 n f b) : Nat.card E ≤ p ^ 7 := by
  have hf : f ≠ 0 := by have := hadm.1.2.1; omega
  have hset := ggKnownSetting_autU hadm
  have hcen : Subgroup.center (e7Data_valid.minGroup (GaloisField 2 f)) = ⊥ := by
    obtain ⟨hcard, -⟩ := card_center_e7 (GaloisField 2 f)
    rw [GaloisField.card 2 f hf] at hcard
    have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 hf
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have hg : Nat.gcd 2 (2 ^ f - 1) = 1 :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega)
    exact Subgroup.eq_bot_of_card_eq _ (by rw [hcard, hg])
  have hEr : E ≤ (ggPsiU .E7 n f).range := fun b hb =>
    ggInnDiagU_mem_range_of_untwisted (Or.inr (Or.inl rfl)) hadm (hdiag b hb)
  have hinj : Function.Injective (ggPsiU .E7 n f) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hset.2.1.trans hcen.le
  have hiso : Function.Injective (e7Isogeny (GaloisField 2 f)) := by
    rw [← MonoidHom.ker_eq_bot_iff, e7Isogeny_ker_eq_center]
    exact hcen
  obtain ⟨hE', hcard⟩ := ciaComap (ggPsiU .E7 n f) hinj hEr hE
  obtain ⟨hE'', hcard'⟩ := ciaMap (e7Isogeny (GaloisField 2 f)) hiso
    (E := (E.comap (ggPsiU .E7 n f) : Subgroup ↥(e7Data_valid.minGroup (GaloisField 2 f)))) hE'
  exact (hcard.symm.trans hcard'.symm).le.trans (ciaBound_E7 hf hp hp2 hreg hE'')

theorem ggKGInndiagCIa_E8
    (n f : ℕ) (hadm : GGKnownAdm .E8 n f) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hreg : GGExcRegime p f) {E : Subgroup (GGAutU .E8 n f)}
    (hE : IsElemAbelian p E) (hdiag : ∀ b ∈ E, GGInnDiagU .E8 n f b) : Nat.card E ≤ p ^ 8 := by
  have hf : f ≠ 0 := by have := hadm.1.2.1; omega
  have hset := ggKnownSetting_autU hadm
  have hEr : E ≤ (ggPsiU .E8 n f).range := fun b hb =>
    ggInnDiagU_mem_range_of_untwisted (Or.inr (Or.inr rfl)) hadm (hdiag b hb)
  have hinj : Function.Injective (ggPsiU .E8 n f) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hset.2.1.trans (center_adjointGroup_eq_bot (τ := .E8) (K := GaloisField 2 f)).le
  obtain ⟨hE', hcard⟩ := ciaComap (ggPsiU .E8 n f) hinj hEr hE
  exact hcard.symm.le.trans (ciaBound_E8 hf hp hp2 hreg
    (E := (E.comap (ggPsiU .E8 n f) : Subgroup ↥(adjointGroup .E8 (GaloisField 2 f)))) hE')

theorem ggKGInndiagCIa_untwisted
    {t : StatedLieTag} (ht : t = .F4 ∨ t = .E7 ∨ t = .E8)
    (n f : ℕ) (hadm : GGKnownAdm t n f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hreg : GGExcRegime p f) {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    (hπ : GGPiCond t p f π) {E : Subgroup (GGAutU t n f)} (hE : IsElemAbelian p E)
    (hdiag : ∀ b ∈ E, GGInnDiagU t n f b) : Nat.card E ≤ GGFixCard p π := by
  have hπ1 : π = 1 := hπ.2.1 ht
  subst hπ1
  rw [ciaFixCard_one hp]
  rcases ht with rfl | rfl | rfl
  · exact ggKGInndiagCIa_F4 n f hadm hp hp2 hreg hE hdiag
  · exact ggKGInndiagCIa_E7 n f hadm hp hp2 hreg hE hdiag
  · exact ggKGInndiagCIa_E8 n f hadm hp hp2 hreg hE hdiag

end CFSG.StandardType
