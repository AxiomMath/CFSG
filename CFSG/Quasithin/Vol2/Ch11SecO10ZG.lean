module

public import CFSG.Quasithin.Vol2.Ch11SecO10ZE
public import CFSG.Quasithin.Vol2.Ch11SecO10S
public import CFSG.Quasithin.Vol2.Ch11SecO10T
public import CFSG.Quasithin.Vol2.Ch11SecO10Y

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 SecE

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G} {z : G}

theorem false_of_autOn_sup (hF : Facts42) (hS : Facts42S3) (hF43 : Facts43) (h701 : Stmt7_0_1)
    (hN : SecA.NatFacts) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1111 : Stmt11_1_1)
    (h1141 : Stmt11_4_1) (hc : Conf11_4_2 T L I n V₁ z) (hn2 : n = 2) {I' : Subgroup G}
    (hfsu : FSU G T (kz L V₁ z) I')
    (hJ : ¬ thompsonJ (ROf T L V₁) ≤ pCoreOf 2 (kz L V₁ z ⊔ T))
    (hA7 : IsAlt 7 (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z)) ∨
      IsHat (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z)) ↥(alternatingGroup (Fin 7)))
    (he : Nonempty (↥(autOn (kz L V₁ z ⊔ T) (fsuV T I')) ≃* alternatingGroup (Fin 7))) :
    False := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h := hc.hyp
  obtain ⟨-, -, -, hTK, hLK⟩ := kz_setting hF hS hF43 h1102 h1110 h1111 h1141 hc
  obtain ⟨hKV, hTV, -, hne⟩ := fsuV_spec h701 hfsu hTK
  obtain ⟨e⟩ := he
  have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have hYs : IsSimpleGroup ↥(autOn (kz L V₁ z ⊔ T) (fsuV T I')) := e.isSimpleGroup
  have hne1 : autOn (kz L V₁ z) (fsuV T I') ≠ ⊥ := by
    intro h0
    apply hne
    intro k hk
    have h1 := SecA.conjV_mem_autOn hk (hKV hk)
    rw [h0, mem_bot] at h1
    exact SecD.mem_centralizer_of_conjV_eq_one (hKV hk) h1
  have hKY := autOn_eq_of_isSimple le_sup_left (sup_le le_normalizer hTK) hYs hne1
  let φ : ↥(kz L V₁ z) →* ↥(autOn (kz L V₁ z ⊔ T) (fsuV T I')) :=
    { toFun := fun k => ⟨SecA.conjV (fsuV T I') k (hKV k.2),
        SecA.conjV_mem_autOn (Subgroup.mem_sup_left k.2) _⟩
      map_one' := Subtype.ext (by ext v; simp [SecA.conjV_apply_coe])
      map_mul' := fun k k' => Subtype.ext (SecA.conjV_mul _ (hKV k.2) (hKV k'.2)) }
  let f : ↥(kz L V₁ z) →* Perm (Fin 7) :=
    (alternatingGroup (Fin 7)).subtype.comp (e.toMonoidHom.comp φ)
  have hf : f.range = alternatingGroup (Fin 7) := by
    apply le_antisymm
    · rintro _ ⟨k, rfl⟩
      exact (e (φ k)).2
    · intro σ hσ
      set w := e.symm ⟨σ, hσ⟩ with hw
      have hwK : (w : MulAut ↥(fsuV T I')) ∈ autOn (kz L V₁ z) (fsuV T I') := by
        rw [hKY]
        exact w.2
      obtain ⟨k, hk, hkV, hke⟩ := SecA.mem_autOn_iff.1 hwK
      have h1 : φ ⟨k, hk⟩ = w := Subtype.ext hke.symm
      refine ⟨⟨k, hk⟩, ?_⟩
      show ((e (φ ⟨k, hk⟩) : alternatingGroup (Fin 7)) : Perm (Fin 7)) = σ
      rw [h1, hw, MulEquiv.apply_symm_apply]
  obtain ⟨K₀, _, _, hK₀, ⟨e₁⟩⟩ := SecA.lOf_quot_SL2 hN h1102 h (Or.inl rfl) hc.vi
  rw [hn2] at hK₀
  obtain ⟨y, hyL, hy5, hy1⟩ := exists_five_lOf hLK f hf hA7 hK₀ e₁
  set x := φ ⟨y, hLK hyL⟩ with hx
  have hx1 : x ≠ 1 := fun h1 => hy1 (by
    show ((e x : alternatingGroup (Fin 7)) : Perm (Fin 7)) = 1
    rw [h1, map_one]
    rfl)
  have hx5 : orderOf x = 5 := by
    refine orderOf_eq_prime ?_ hx1
    rw [hx, ← map_pow]
    have : (⟨y, hLK hyL⟩ : ↥(kz L V₁ z)) ^ 5 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, ← hy5, pow_orderOf_eq_one, OneMemClass.coe_one])
    rw [this, map_one]
  have hRT : ROf T L V₁ ≤ T := SecD.ROf_le_T h V₁
  have hRY : autOn (ROf T L V₁) (fsuV T I') ≤ autOn (kz L V₁ z ⊔ T) (fsuV T I') :=
    SecA.autOn_mono (hRT.trans le_sup_right)
  have hP2 : IsPGroup 2 ((autOn (ROf T L V₁) (fsuV T I')).subgroupOf
      (autOn (kz L V₁ z ⊔ T) (fsuV T I'))) :=
    (isPGroup_autOn_of (h.fsu.sylow.1.to_le hRT)).comap_of_injective _
      (Subgroup.subtype_injective _)
  have hLR : LOf L V₁ ≤ Subgroup.normalizer (ROf T L V₁ : Set G) := fun w hw =>
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hw)
  have hxN : (x : MulAut ↥(fsuV T I')) ∈
      Subgroup.normalizer (autOn (ROf T L V₁) (fsuV T I') : Set (MulAut ↥(fsuV T I'))) :=
    SecS.autOn_le_normalizer hLR (SecA.conjV_mem_autOn hyL (hKV (hLK hyL)))
  have hxP : x ∈ Subgroup.normalizer (((autOn (ROf T L V₁) (fsuV T I')).subgroupOf
      (autOn (kz L V₁ z ⊔ T) (fsuV T I')) : Set _)) := by
    rw [mem_normalizer_iff]
    intro p
    rw [mem_subgroupOf, mem_subgroupOf]
    exact mem_normalizer_iff.1 hxN p
  have hPbot := eq_bot_of_two_of_five_iso e hP2 hx5 hxP
  have hR₁V : ROf T L V₁ ≤ Subgroup.centralizer (fsuV T I' : Set G) := by
    intro r hr
    have hrV := hTV (hRT hr)
    have h1 : (⟨SecA.conjV (fsuV T I') r hrV, hRY (SecA.conjV_mem_autOn hr hrV)⟩ :
        ↥(autOn (kz L V₁ z ⊔ T) (fsuV T I'))) ∈ (autOn (ROf T L V₁) (fsuV T I')).subgroupOf
          (autOn (kz L V₁ z ⊔ T) (fsuV T I')) := SecA.conjV_mem_autOn hr hrV
    rw [hPbot, mem_bot] at h1
    exact SecD.mem_centralizer_of_conjV_eq_one hrV (congrArg Subtype.val h1)
  apply hJ
  intro j hj
  have hjR : j ∈ ROf T L V₁ := (iSup₂_le fun A hA => hA.1 : thompsonJ (ROf T L V₁) ≤ _) hj
  exact inf_centralizer_fsuV_le_kz hF hS hF43 h701 h1102 h1110 h1111 h1141 hc hfsu
    ⟨hRT hjR, hR₁V hjR⟩

end CFSG.Quasithin.Vol2.Ch11.O10
