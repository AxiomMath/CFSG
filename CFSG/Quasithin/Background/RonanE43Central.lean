module

public import CFSG.Quasithin.Background.RonanE43Basic
public import CFSG.LieType.BorelTits.CentralQuotient

public section

namespace CFSG.Quasithin.RonanE43

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.RonanE42

variable {G : Type} [Group G] [Finite G] {Γ : Type} [Group Γ]

theorem card_pCoreOf_le_comap (π : G →* Γ) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center G) (hodd : Nat.Coprime (Nat.card π.ker) 2)
    (Y : Subgroup Γ) : Nat.card (pCoreOf 2 Y) ≤ Nat.card (pCoreOf 2 (Y.comap π)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite Γ := Finite.of_surjective π hπ
  let e : G ⧸ π.ker ≃* Γ := QuotientGroup.quotientKerEquivOfSurjective π hπ
  set M : Subgroup (G ⧸ π.ker) := Y.comap (e : G ⧸ π.ker →* Γ) with hM
  have hcomp : (e : G ⧸ π.ker →* Γ).comp (QuotientGroup.mk' π.ker) = π := by
    ext g
    rfl
  have hcomap : M.comap (QuotientGroup.mk' π.ker) = Y.comap π := by
    rw [hM, Subgroup.comap_comap, hcomp]
  have hMmap : M = Y.map e.symm.toMonoidHom := Subgroup.comap_equiv_eq_map_symm e Y
  have h1 := CFSG.LieType.BorelTits.pCoreOf_le_map_pCoreOf_comap (r := 2) π.ker hker hodd M
  rw [hcomap] at h1
  have h2 : Nat.card (pCoreOf 2 M) = Nat.card (pCoreOf 2 Y) := by
    rw [hMmap, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 e.symm Y]
    exact Subgroup.card_map_of_injective e.symm.injective
  rw [← h2]
  exact (Subgroup.card_le_of_le h1).trans (Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _))

theorem card_map_eq_of_odd_ker (π : G →* Γ) (hodd : Nat.Coprime (Nat.card π.ker) 2)
    {T : Subgroup G} (hT : IsPGroup 2 T) : Nat.card (T.map π) = Nat.card T := by
  have hinj : Function.Injective (π.comp T.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro t ht
    have ht1 : π (t : G) = 1 := ht
    have htk : (t : G) ∈ π.ker := ht1
    obtain ⟨n, hn⟩ := hT t
    have h1 : orderOf (t : G) ∣ Nat.card π.ker := by
      have := Subgroup.orderOf_dvd_natCard π.ker htk
      exact this
    have h2 : orderOf (t : G) ∣ 2 ^ n := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg Subtype.val hn
      simpa using this
    have h3 : orderOf (t : G) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right n (Nat.Coprime.coprime_dvd_left h1 hodd)) h2
    have : (t : G) = 1 := orderOf_eq_one_iff.mp h3
    exact Subtype.ext this
  have hrange : (π.comp T.subtype).range = T.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem isSylowIn_map (π : G →* Γ) (hπ : Function.Surjective π)
    {T : Subgroup G} (hT : IsSylowIn 2 T ⊤) : ¬ 2 ∣ (T.map π).index := by
  have h1 : (T.map π).index ∣ T.index := Subgroup.index_map_dvd T hπ
  have h2 : ¬ 2 ∣ T.index := by
    have := hT.not_dvd_relIndex
    rwa [Subgroup.relIndex_top_right] at this
  exact fun h => h2 (h.trans h1)

variable [Finite Γ]

theorem aParam_le_of_central_family (V : Type) [CommGroup V] [Finite V] (ρ : G →* MulAut V)
    (hρ : Function.Injective ρ) (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) {T L : Subgroup G}
    (hT : IsSylowIn 2 T ⊤) (hLF : L = CFSG.generalizedFitting G) (hLq : CFSG.IsQuasisimple ↥L)
    (hLT : L ⊔ T = ⊤) (hlt : fixV ρ.range < fixV (T.map ρ))
    (π : G →* Γ) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    (hodd : Nat.Coprime (Nat.card π.ker) 2) {S₀ : Subgroup Γ} (hS₀ : IsSylowIn 2 S₀ ⊤)
    (F : Finset (Subgroup Γ)) (hF : F.Nonempty) (hSF : ∀ Y ∈ F, S₀ ≤ Y)
    (h2F : ∀ Y ∈ F, Nat.card S₀ ≤ 2 * Nat.card (pCoreOf 2 Y)) (hgen : (⨆ Y ∈ F, Y) = ⊤) :
    aParam ρ.range ≤ F.card := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 (T.map π) := hT.isPGroup.map π
  let PT : Sylow 2 Γ := hTp.toSylow (isSylowIn_map π hπ hT)
  have hS0idx : ¬ 2 ∣ S₀.index := by
    have := hS₀.not_dvd_relIndex
    rwa [Subgroup.relIndex_top_right] at this
  let P0 : Sylow 2 Γ := hS₀.isPGroup.toSylow hS0idx
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq Γ P0 PT
  have hSc : S₀.map (MulAut.conj c).toMonoidHom = T.map π := by
    have := congrArg (fun Q : Sylow 2 Γ => (Q : Subgroup Γ)) hc
    exact this
  let conjc : Subgroup Γ → Subgroup Γ := fun Y => Y.map (MulAut.conj c).toMonoidHom
  let Δ : Finset (Subgroup G) := F.image (fun Y => (conjc Y).comap π)
  have hΔT : ∀ H ∈ Δ, T ≤ H := by
    intro H hH
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hH
    intro t ht
    rw [Subgroup.mem_comap]
    have h1 : π t ∈ T.map π := Subgroup.mem_map_of_mem π ht
    rw [← hSc] at h1
    exact Subgroup.map_mono (hSF Y hY) h1
  have h2 : ∀ H ∈ Δ, Nat.card T ≤ 2 * Nat.card (pCoreOf 2 H) := by
    intro H hH
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hH
    have e1 : Nat.card T = Nat.card S₀ := by
      rw [← card_map_eq_of_odd_ker π hodd hT.isPGroup, ← hSc]
      exact (Subgroup.card_map_of_injective (MulAut.conj c).injective)
    have e2 : Nat.card (pCoreOf 2 (conjc Y)) = Nat.card (pCoreOf 2 Y) := by
      have := CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj c) Y
      show Nat.card (pCoreOf 2 (Y.map (MulAut.conj c).toMonoidHom)) = _
      rw [this]
      exact Subgroup.card_map_of_injective (MulAut.conj c).injective
    have e3 := card_pCoreOf_le_comap π hπ hker hodd (conjc Y)
    calc Nat.card T = Nat.card S₀ := e1
      _ ≤ 2 * Nat.card (pCoreOf 2 Y) := h2F Y hY
      _ = 2 * Nat.card (pCoreOf 2 (conjc Y)) := by rw [e2]
      _ ≤ 2 * Nat.card (pCoreOf 2 ((conjc Y).comap π)) := Nat.mul_le_mul_left _ e3
  have hΔgen : (⨆ H ∈ Δ, H) = ⊤ := by
    set X : Subgroup G := ⨆ H ∈ Δ, H with hX
    have hle : ∀ Y ∈ F, (conjc Y).comap π ≤ X := fun Y hY =>
      le_iSup₂_of_le ((conjc Y).comap π) (Finset.mem_image.mpr ⟨Y, hY, rfl⟩) le_rfl
    obtain ⟨Y0, hY0⟩ := hF
    have hXker : π.ker ≤ X := by
      intro g hg
      apply hle Y0 hY0
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hg]
      exact Subgroup.one_mem _
    have hXmap : X.map π = ⊤ := by
      rw [eq_top_iff]
      have h1 : (⊤ : Subgroup Γ) ≤ (⨆ Y ∈ F, conjc Y) := by
        have h3 : (⨆ Y ∈ F, Y) ≤ (⨆ Y ∈ F, conjc Y).comap (MulAut.conj c).toMonoidHom :=
          iSup₂_le fun Y hY y hy =>
            Subgroup.mem_comap.mpr
              (Subgroup.mem_iSup_of_mem Y (Subgroup.mem_iSup_of_mem hY
                (Subgroup.mem_map_of_mem _ hy)))
        rw [hgen] at h3
        intro x _
        have h4 := Subgroup.mem_comap.mp (h3 (Subgroup.mem_top ((MulAut.conj c).symm x)))
        rwa [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at h4
      refine h1.trans (iSup₂_le fun Y hY => ?_)
      calc conjc Y = ((conjc Y).comap π).map π :=
            (Subgroup.map_comap_eq_self_of_surjective hπ _).symm
        _ ≤ X.map π := Subgroup.map_mono (hle Y hY)
    have := Subgroup.comap_map_eq_self hXker
    rw [hXmap, Subgroup.comap_top] at this
    exact this.symm
  have hmain := aParam_le_card_of_family V ρ hρ hO2 Δ hT hLF hLq hLT hlt hΔgen hΔT h2
  exact hmain.trans Finset.card_image_le


theorem coprime_card_center_of_pCore_bot (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥)
    {K : Subgroup G} (hK : K ≤ Subgroup.center G) : Nat.Coprime (Nat.card K) 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hxc : (x : G) ∈ Subgroup.center G := hK x.2
  have hord : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  have hp : IsPGroup 2 (Subgroup.zpowers (x : G)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord]; simp
  haveI hNn : (Subgroup.zpowers (x : G)).Normal := ⟨fun n hn g => by
    have hnc : n ∈ Subgroup.center G := Subgroup.zpowers_le.mpr hxc hn
    have h1 : g * n * g⁻¹ = n := by
      have := Subgroup.mem_center_iff.mp hnc g
      rw [this]; group
    rw [h1]; exact hn⟩
  have hle : Subgroup.zpowers (x : G) ≤ pCoreOf 2 (⊤ : Subgroup G) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_top
      (by rw [(Subgroup.normalizer_eq_top_iff).mpr hNn]) hp
  rw [hO2] at hle
  have hx1 : (x : G) = 1 := Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers _))
  rw [hx1, orderOf_one] at hord
  omega

theorem exists_central_hom {L : Subgroup G} (hLtop : L = ⊤)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* Γ) (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥) :
    ∃ π : G →* Γ, Function.Surjective π ∧ π.ker ≤ Subgroup.center G ∧
      Nat.Coprime (Nat.card π.ker) 2 := by
  subst hLtop
  let ι : ↥(⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
  let π : G →* Γ := e.toMonoidHom.comp
    ((QuotientGroup.mk' (Subgroup.center ↥(⊤ : Subgroup G))).comp ι.symm.toMonoidHom)
  have hsurj : Function.Surjective π :=
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp ι.symm.surjective)
  have hker : π.ker ≤ Subgroup.center G := by
    intro g hg
    have h1 : e (QuotientGroup.mk' (Subgroup.center ↥(⊤ : Subgroup G)) (ι.symm g)) = 1 := hg
    rw [map_eq_one_iff e e.injective, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at h1
    rw [Subgroup.mem_center_iff]
    intro y
    apply ι.symm.injective
    rw [map_mul, map_mul]
    exact (Subgroup.mem_center_iff.mp h1 (ι.symm y))
  exact ⟨π, hsurj, hker, coprime_card_center_of_pCore_bot hO2 hker⟩

end CFSG.Quasithin.RonanE43
