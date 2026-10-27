module

public import CFSG.Quasithin.Vol2.Ch11SecO10ZH
public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.Vol2.Ch10SecB4Aux
public import CFSG.Quasithin.Vol2.Ch11SecO10R

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 SecE
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G} {z : G}

theorem exists_not_comm_alt7 : ∃ a b : alternatingGroup (Fin 7), a * b ≠ b * a :=
  ⟨⟨Equiv.swap 0 2 * Equiv.swap 0 1, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩,
    ⟨Equiv.swap 0 3 * Equiv.swap 0 1, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩,
    fun h => by
      have := congrArg Subtype.val h
      revert this
      decide⟩

theorem not_surjective_sl {Y : Type*} [Group Y] [Finite Y] (hY : Nat.card Y = 2520) {m : ℕ}
    (hm : m = 4 ∨ m = 5) (π : ↥(CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2)) →* Y) :
    ¬ Function.Surjective π := by
  intro hπ
  have e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m (ZMod 2)
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) :=
    SecA.isSimpleGroup_SL_zmod_two (by omega)
  have : IsSimpleGroup ↥(CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2)) := e.symm.isSimpleGroup
  have hcard := Nat.card_congr e.toEquiv
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
  · have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 h
    have h1 := Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ⟩)
    rw [hY, ← hcard] at h1
    rcases card_sl_zmod_two hm with h2 | h2 <;> omega
  · have h1 : ∀ y : Y, y = 1 := fun y => by
      obtain ⟨x, rfl⟩ := hπ y
      exact (MonoidHom.mem_ker).1 (h ▸ Subgroup.mem_top x)
    have h2 : Nat.card Y = 1 := Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (h1 a).trans (h1 b).symm⟩,
      ⟨1⟩⟩
    omega

theorem false_of_sum (hF : Facts42) (hS : Facts42S3) (hF43 : Facts43) (h701 : Stmt7_0_1)
    (h51 : AsB51) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1111 : Stmt11_1_1)
    (h1141 : Stmt11_4_1) (hc : Conf11_4_2 T L I n V₁ z) {I' : Subgroup G}
    (hfsu : FSU G T (kz L V₁ z) I')
    (hJ : ¬ thompsonJ (ROf T L V₁) ≤ pCoreOf 2 (kz L V₁ z ⊔ T))
    (hcv : I' ⊓ Subgroup.centralizer (kz L V₁ z : Set G) = ⊥)
    (he : Nonempty (↥(autOn (kz L V₁ z) (fsuV T I')) ≃* alternatingGroup (Fin 7))) {t : G}
    (htT : t ∈ T) (hsum : fsuV T I' = I' ⊔ CFSG.conjugate I' t)
    (hinf : I' ⊓ CFSG.conjugate I' t = ⊥)
    (hni : ¬ IsXSectionIso₂ (kz L V₁ z) I' ⊥ (CFSG.conjugate I' t) ⊥) : False := by
  obtain ⟨-, -, -, hTK, -⟩ := kz_setting hF hS hF43 h1102 h1110 h1111 h1141 hc
  obtain ⟨hKV, -, -, -⟩ := fsuV_spec h701 hfsu hTK
  obtain ⟨hcomm, hff⟩ := isFFModule_fsuV_kz hF hS hF43 h701 h1102 h1110 h1111 h1141 hc hfsu hJ
  have hVe := isElemAbelian_fsuV_of_fsu hfsu
  obtain ⟨e⟩ := he
  have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have hcard : Nat.card ↥(autOn (kz L V₁ z) (fsuV T I')) = 2520 := by
    rw [Nat.card_congr e.toEquiv, card_alt7]
  have hq : CFSG.IsQuasisimple ↥(autOn (kz L V₁ z) (fsuV T I')) := by
    obtain ⟨a, b, hab⟩ := exists_not_comm_alt7
    refine isQuasisimple_of_simple e.isSimpleGroup ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  have hL0 : conjClosure (kz L V₁ z) T = kz L V₁ z := Ch10.SecB.conjClosure_eq_self hTK
  have hirr := hfsu.irrPlus
  rw [hL0] at hirr
  have hLA : kz L V₁ z ≤ Subgroup.normalizer (I' : Set G) := hirr.2.2.1
  have hirrA : ∀ J : Subgroup G, J ≤ I' → kz L V₁ z ≤ Subgroup.normalizer (J : Set G) →
      J = ⊥ ∨ J = I' := by
    intro J hJ hKJ
    rcases hirr.2.2.2.2.2.1 J (by rw [hcv]; exact bot_le) hJ hKJ with h | h
    · exact Or.inl (h.trans hcv)
    · exact Or.inr h
  have hntA : ¬ I' ≤ Subgroup.centralizer (kz L V₁ z : Set G) := fun hle =>
    hirr.2.1 (by rw [← inf_of_le_left hle, hcv])
  have htK := hTK htT
  exact InternalSec.not_isFFModule_normalizer_autOn_of_sum (V := fsuV T I') h51
    (fun v hv => hVe.2 v hv) hKV hq (sqtkGroup_autOn_of_fsu hfsu hKV hcard)
    (hsum ▸ le_sup_left) (hsum ▸ le_sup_right) hsum.symm hinf hLA
    (le_normalizer_conjugate hLA htK) hirrA (irr_conjugate htK hirrA) hntA
    (not_le_centralizer_conjugate htK hntA) hni
    (fun m hm π => not_surjective_sl hcard hm π) hff

end CFSG.Quasithin.Vol2.Ch11.O10
