module

public import CFSG.Quasithin.Vol2.Ch10T326CFsu
public import CFSG.Quasithin.H13.StatementsCh7
public import CFSG.Quasithin.Background.BlueprintB2Reduced

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13

variable {G : Type} [Group G]

theorem map_map_symm (σ : G ≃* G) (J : Subgroup G) :
    (J.map σ.symm.toMonoidHom).map σ.toMonoidHom = J := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, MulEquiv.symm_symm,
    MulEquiv.apply_symm_apply]

theorem map_symm_map (σ : G ≃* G) (J : Subgroup G) :
    (J.map σ.toMonoidHom).map σ.symm.toMonoidHom = J := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, MulEquiv.symm_symm,
    MulEquiv.symm_apply_apply]

theorem isIrrPlusIn_map {X A Y I : Subgroup G} (σ : G ≃* G) (h : IsIrrPlusIn X A Y I) :
    IsIrrPlusIn (X.map σ.toMonoidHom) (A.map σ.toMonoidHom) (Y.map σ.toMonoidHom)
      (I.map σ.toMonoidHom) := by
  obtain ⟨hIA, hI0, hXI, hcomm, hlt, hmax, hhom⟩ := h
  have hinj : Function.Injective σ.toMonoidHom := σ.injective
  have hN : ∀ J : Subgroup G, (Subgroup.normalizer (J : Set G)).map σ.toMonoidHom =
      Subgroup.normalizer ((J.map σ.toMonoidHom : Subgroup G) : Set G) := fun J =>
    Subgroup.map_normalizer_eq_of_bijective J (σ.bijective : Function.Bijective σ.toMonoidHom)
  have hIC : (I ⊓ Subgroup.centralizer (X : Set G)).map σ.toMonoidHom =
      I.map σ.toMonoidHom ⊓
        Subgroup.centralizer ((X.map σ.toMonoidHom : Subgroup G) : Set G) := by
    rw [Subgroup.map_inf _ _ _ hinj, map_centralizer_equiv]
  have hAC : (A ⊓ Subgroup.centralizer (X : Set G)).map σ.toMonoidHom =
      A.map σ.toMonoidHom ⊓
        Subgroup.centralizer ((X.map σ.toMonoidHom : Subgroup G) : Set G) := by
    rw [Subgroup.map_inf _ _ _ hinj, map_centralizer_equiv]
  refine ⟨Subgroup.map_mono hIA,
    fun h0 => hI0 ((Subgroup.map_eq_bot_iff_of_injective I hinj).mp h0),
    (Subgroup.map_mono hXI).trans (hN I).le, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, hcomm]
  · rw [← hIC]
    exact (Subgroup.map_lt_map_iff_of_injective hinj).mpr hlt
  · intro J hJ1 hJ2 hJ3
    obtain ⟨J₀, rfl⟩ : ∃ J₀ : Subgroup G, J₀.map σ.toMonoidHom = J :=
      ⟨J.map σ.symm.toMonoidHom, map_map_symm σ J⟩
    rw [← hIC] at hJ1 ⊢
    rw [← hN] at hJ3
    have h1 := (Subgroup.map_le_map_iff_of_injective hinj).mp hJ1
    have h2 := (Subgroup.map_le_map_iff_of_injective hinj).mp hJ2
    have h3 := (Subgroup.map_le_map_iff_of_injective hinj).mp hJ3
    rcases hmax J₀ h1 h2 h3 with h | h
    · exact Or.inl (congrArg (fun K : Subgroup G => K.map σ.toMonoidHom) h)
    · exact Or.inr (congrArg (fun K : Subgroup G => K.map σ.toMonoidHom) h)
  · intro J hJ1 hJ2 hJ3 hJ4
    obtain ⟨J₀, rfl⟩ : ∃ J₀ : Subgroup G, J₀.map σ.toMonoidHom = J :=
      ⟨J.map σ.symm.toMonoidHom, map_map_symm σ J⟩
    rw [← hAC] at hJ1 hJ2 hJ4 ⊢
    rw [← hN] at hJ3
    rw [← map_conjClosure, ← Subgroup.map_sup] at hJ2
    rw [← Subgroup.map_sup] at hJ4 ⊢
    have h1 := (Subgroup.map_le_map_iff_of_injective hinj).mp hJ1
    have h2 := (Subgroup.map_le_map_iff_of_injective hinj).mp hJ2
    have h3 := (Subgroup.map_le_map_iff_of_injective hinj).mp hJ3
    have h4 := isXSectionIso_map σ.symm hJ4
    simp only [map_symm_map] at h4
    exact Subgroup.map_mono (hhom J₀ h1 h2 h3 h4)

theorem le_normalizer_reducedAggregate [Finite G] (X : Subgroup G) :
    X ≤ Subgroup.normalizer (reducedAggregate X : Set G) := by
  intro g hg
  have hn := (primeReducedAggregate_normal_elementaryAbelian (E := ↥X) 2).1
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨y', hy', rfl⟩
    exact ⟨⟨g, hg⟩ * y' * ⟨g, hg⟩⁻¹, hn.conj_mem _ hy' _, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    refine ⟨⟨g, hg⟩⁻¹ * z * ⟨g, hg⟩, ?_, ?_⟩
    · have h1 := hn.conj_mem _ hz (⟨g, hg⟩⁻¹)
      rwa [inv_inv] at h1
    · have h1 : (z : G) = g * y * g⁻¹ := hzy
      show g⁻¹ * (z : G) * g = y
      rw [h1]
      group

theorem fsu_conjugate [Finite G] {T L I : Subgroup G} (hfsu : FSU G T L I) {x : G}
    (hx : x ∈ T) : FSU G T L (CFSG.conjugate I x) := by
  have hx' : x⁻¹ ∈ T := T.inv_mem hx
  have hL₀ : (conjClosure L T).map (MulAut.conj x⁻¹).toMonoidHom = conjClosure L T :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjClosure L T hx')
  have hR : (reducedAggregate (L ⊔ T)).map (MulAut.conj x⁻¹).toMonoidHom =
      reducedAggregate (L ⊔ T) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (le_normalizer_reducedAggregate (L ⊔ T) (Subgroup.mem_sup_right hx'))
  have hT : T.map (MulAut.conj x⁻¹).toMonoidHom = T :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hx')
  have h := isIrrPlusIn_map (MulAut.conj x⁻¹) hfsu.irrPlus
  rw [hL₀, hR, hT] at h
  exact { hfsu with irrPlus := h }

theorem fsuV_conjugate {T I : Subgroup G} {x : G} (hx : x ∈ T) :
    fsuV T (CFSG.conjugate I x) = fsuV T I := by
  have hx' : x⁻¹ ∈ T := T.inv_mem hx
  have hT : T.map (MulAut.conj x⁻¹).toMonoidHom = T :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hx')
  have hV : (conjClosure I T).map (MulAut.conj x⁻¹).toMonoidHom = conjClosure I T :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjClosure I T hx')
  have h := map_conjClosure (MulAut.conj x⁻¹) I T
  rw [hT, hV] at h
  exact h.symm

theorem fsuVM_conjugate {T L I : Subgroup G} {x : G} (hx : x ∈ T) :
    fsuVM T L (CFSG.conjugate I x) = fsuVM T L I := by
  show conjClosure (fsuV T (CFSG.conjugate I x)) (fsuM T L) = _
  rw [fsuV_conjugate hx]

theorem fsuUL_conjugate {T L I : Subgroup G} {x : G} (hx : x ∈ T) :
    fsuUL T L (CFSG.conjugate I x) = fsuUL T L I := by
  show ⁅fsuVM T L (CFSG.conjugate I x), L⁆ = _
  rw [fsuVM_conjugate hx]

theorem fsuCVM_conjugate {T L I : Subgroup G} {x : G} (hx : x ∈ T) :
    fsuCVM T L (CFSG.conjugate I x) = fsuCVM T L I := by
  show fsuVM T L (CFSG.conjugate I x) ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = _
  rw [fsuVM_conjugate hx]

theorem card_conjugate (I : Subgroup G) (x : G) :
    Nat.card ↥(CFSG.conjugate I x) = Nat.card ↥I :=
  Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective

end CFSG.Quasithin.Vol2.Ch10
