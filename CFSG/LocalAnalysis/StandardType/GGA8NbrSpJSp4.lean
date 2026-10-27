module

public import CFSG.LocalAnalysis.StandardType.GGA8NbrSpJClass
public import CFSG.LocalAnalysis.StandardType.MarkingClassical

public section

namespace CFSG.StandardType.A8Coord

open CFSG.Assembly CFSG.Open CFSG.StandardType

lemma a8j4_card_dvd_quotient_center {G : Type} [Group G] {J K : Subgroup G}
    (hJK : J ≤ K) (hdisj : J ⊓ (Subgroup.center K).map K.subtype = ⊥) :
    Nat.card J ∣ Nat.card (K ⧸ Subgroup.center K) := by
  have hker : ((QuotientGroup.mk' (Subgroup.center K)).comp
      (Subgroup.inclusion hJK)).ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx1 : (QuotientGroup.mk (Subgroup.inclusion hJK x) : (↥K ⧸ Subgroup.center K)) = 1 := by
      have h := MonoidHom.mem_ker.mp hx
      simpa [MonoidHom.comp_apply, QuotientGroup.mk'_apply] using h
    have hxK : Subgroup.inclusion hJK x ∈ Subgroup.center K :=
      (QuotientGroup.eq_one_iff (Subgroup.inclusion hJK x)).mp hx1
    have hxZK : (x : G) ∈ (Subgroup.center K).map K.subtype :=
      Subgroup.mem_map.mpr ⟨Subgroup.inclusion hJK x, hxK, rfl⟩
    have hxinf : (x : G) ∈ J ⊓ (Subgroup.center K).map K.subtype := ⟨x.2, hxZK⟩
    rw [hdisj, Subgroup.mem_bot] at hxinf
    exact Subtype.ext (by simpa using hxinf)
  exact Subgroup.card_dvd_of_injective _ ((MonoidHom.ker_eq_bot_iff _).mp hker)

theorem a8j4_not_thirteen_dvd_centerQuotient {G : Type} [Group G] {K : Subgroup G}
    (hKm : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 9 2 1) :
    ¬ 13 ∣ Nat.card (K ⧸ Subgroup.center K) := by
  obtain ⟨-, K', hfield, hfinite, hcard, ⟨e⟩⟩ := hKm
  letI : Field K' := hfield
  letI : Finite K' := hfinite
  letI : Fintype K' := Fintype.ofFinite K'
  have hq : Fintype.card K' = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have hcardSL : Nat.card (StatedSL 9 K') =
      Nat.card (Matrix.SpecialLinearGroup (Fin 9) K') :=
    (Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 9 K').toEquiv).symm
  have hcardproj : Nat.card (K ⧸ Subgroup.center K) =
      Nat.card (StatedProj (StatedSL 9 K')) := Nat.card_congr e.toEquiv
  have hdvd : Nat.card (StatedProj (StatedSL 9 K')) ∣ Nat.card (StatedSL 9 K') :=
    Subgroup.card_quotient_dvd_card _
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 9) K') =
      (∏ i : Fin 9, (2 ^ 9 - 2 ^ (i : ℕ))) / (2 - 1) := by
    rw [Matrix.card_SL_field (𝔽 := K') 9, hq]
  have hnot : ¬ 13 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 9) K') := by
    rw [hSL]
    norm_num [Fin.prod_univ_succ]
  intro h13
  have h13' : 13 ∣ Nat.card (StatedProj (StatedSL 9 K')) := hcardproj ▸ h13
  have h13'' : 13 ∣ Nat.card (StatedSL 9 K') := h13'.trans hdvd
  exact hnot (hcardSL ▸ h13'')

private theorem a8j4_block_not_le_K {G : Type} [Group G]
    {m : ℕ} (hm : m = 2) (Φ : StatedSp m (GaloisField 2 3) →* G)
    (hΦinj : Function.Injective Φ)
    {K : Subgroup G}
    (hKm : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 9 2 1)
    (hle : Φ.range ≤ K) : False := by
  subst hm
  haveI : CharP (GaloisField 2 3) 2 := inferInstance
  have hcenterSp : Subgroup.center (StatedSp 2 (GaloisField 2 3)) = ⊥ := by
    rw [CFSG.LieType.Universal.Symplectic.center_eq,
      CFSG.LieType.SteinbergBR.EvenSp.statedScalars_subgroupOf_statedSp (n := 2) (by norm_num)]
  have hZK : Φ.range ⊓ (Subgroup.center K).map K.subtype = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    obtain ⟨hgJ, hgZ⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hgJ
    rw [← hy] at hgZ
    obtain ⟨k, hkcenter, hkval⟩ := Subgroup.mem_map.mp hgZ
    have hkval' : (k : G) = Φ y := hkval
    have hcommK : ∀ z : StatedSp 2 (GaloisField 2 3), Φ z * Φ y = Φ y * Φ z := by
      intro z
      have hzK : Φ z ∈ K := hle (MonoidHom.mem_range.mpr ⟨z, rfl⟩)
      have h := Subgroup.mem_center_iff.mp hkcenter ⟨Φ z, hzK⟩
      have h' := congrArg (fun t : ↥K => (t : G)) h
      simp only [Subgroup.coe_mul] at h'
      simpa only [hkval'] using h'
    have hycent : y ∈ Subgroup.center (StatedSp 2 (GaloisField 2 3)) := by
      rw [Subgroup.mem_center_iff]
      intro z
      exact hΦinj (by rw [map_mul, map_mul]; exact hcommK z)
    rw [hcenterSp, Subgroup.mem_bot] at hycent
    rw [hycent, map_one] at hy
    exact hy.symm
  have hcardJ : Nat.card Φ.range = Nat.card (StatedSp 2 (GaloisField 2 3)) :=
    (Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv).symm
  have h13J : 13 ∣ Nat.card Φ.range := by
    rw [hcardJ, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two,
      GaloisField.card 2 3 (by norm_num)]
    norm_num
  have hdvd : Nat.card Φ.range ∣ Nat.card (K ⧸ Subgroup.center K) :=
    a8j4_card_dvd_quotient_center hle hZK
  exact a8j4_not_thirteen_dvd_centerQuotient hKm (h13J.trans hdvd)

theorem ggA8Nbr_spZblock_not_le_K {G : Type} [Group G] [Finite G]
    {ψ : StatedSp 3 (GaloisField 2 3) →* G} (hψ : Function.Injective ψ)
    (A₀ : StatedSp 3 (GaloisField 2 3)) {β : Fin 3 → ZMod 7}
    (hZ : (CoordSp.spClass β 0).card = 2) {K : Subgroup G}
    (hKm : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 9 2 1)
    (hle : ((CoordSp.blockSp (F := GaloisField 2 3) (CoordSp.spClass β 0)).range).map
      (CoordSp.frameConj ψ A₀) ≤ K) : False := by
  let s : Finset (Fin 3) := CoordSp.spClass β 0
  have hsc : s.card = 2 := hZ
  let Φ : StatedSp s.card (GaloisField 2 3) →* G :=
    (CoordSp.frameConj ψ A₀).comp (CoordSp.blockSp (F := GaloisField 2 3) s)
  have hΦinj : Function.Injective Φ := fun a b hab =>
    CoordSp.blockSp_injective s (CoordSp.frameConj_injective hψ A₀ hab)
  have hle' : Φ.range ≤ K := by
    dsimp only [Φ]
    rw [← MonoidHom.map_range (CoordSp.frameConj ψ A₀)
      (CoordSp.blockSp (F := GaloisField 2 3) s)]
    exact hle
  exact a8j4_block_not_le_K hsc Φ hΦinj hKm hle'

end CFSG.StandardType.A8Coord

end
