module

public import CFSG.Quasithin.Vol2.Ch10SecALiftMain
public import CFSG.Quasithin.Vol2.Ch10SecALiftConj
public import CFSG.Quasithin.Vol2.Ch10SecALiftSyl

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem mem_centralizer_of_case_one (hyp : Ch10.Hyp10 G T L I) {n : ℕ}
    (h1 : Ch10.Case10_1_1One T L I n) {x : G} (hxU : x ∈ fsuUL T L I)
    (hx : ∀ s ∈ T ⊓ L, s * x * s⁻¹ * x⁻¹ ∈ fsuCVM T L I) :
    x ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hUab, F, _, _, hF, π, hR⟩ := h1
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  obtain ⟨β, hβs, hβk, hβe⟩ := exists_beta_of_realizesVia_nat hR
  have hloc := hyp.fsu.maximal.1
  have hLV : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I)
  have hLU : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_normalizer_commutator hLV Subgroup.le_normalizer
  have hUV : fsuUL T L I ≤ fsuVM T L I := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  have hel := isElemAbelian_fsuVM hyp
  have hM : ∀ m : ↥(fsuUL T L I), m ^ 2 = 1 := fun m =>
    Subtype.ext (by simpa using hel.2 _ (hUV m.2))
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    apply FFModel.nat_faithful _ γ
    intro m _
    obtain ⟨w, rfl⟩ := hβs m
    have h1 : ((π γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) w = w := by
      rw [hγ]
      rfl
    have h := hβe γ w
    rw [h1] at h
    exact Subgroup.mem_bot.mpr (mul_inv_eq_one.mpr h.symm)
  set eρ : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(autOn L (fsuUL T L I)) :=
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).trans
      (MulEquiv.ofBijective π ⟨hπinj, hR.1⟩) with heρ
  set ρ : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut ↥(fsuUL T L I) :=
    (autOn L (fsuUL T L I)).subtype.comp eρ.toMonoidHom with hρ
  have hρe : ∀ γ w, β (ρ γ w) = Multiplicative.ofAdd
      ((γ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β w))) := fun γ w =>
    hβe (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F γ) w
  have hZ : ∀ γ, ∀ z ∈ Ch10.cV1 T L I, ρ γ z = z := by
    intro γ z hz
    obtain ⟨g, hgL, hg⟩ := mem_autOn_iff'.mp (eρ γ).2
    have hzL : (z : G) ∈ Subgroup.centralizer (L : Set G) :=
      Subgroup.centralizer_le (le_fsuL0 T L) (Subgroup.mem_subgroupOf.mp hz)
    apply Subtype.ext
    show ((((eρ γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) z : ↥(fsuUL T L I)) : G) =
      (z : G)
    rw [← hg, coe_conjAct_apply', Subgroup.mem_centralizer_iff.mp hzL g hgL]
    group
  set Q' := (autOn (T ⊓ L) (fsuUL T L I)).subgroupOf (autOn L (fsuUL T L I)) with hQ'def
  have hQ' : Q' = ((T ⊓ L).subgroupOf L).map (autOnHomOf hLU) :=
    autOn_subgroupOf_eq_map (W := fsuUL T L I) (inf_le_right : T ⊓ L ≤ L) hLU
  set P := Q'.comap eρ.toMonoidHom with hPdef
  have hsylTL := isSylowTwoOf_inf hloc
  have hP2 : IsPGroup 2 P := by
    have hle : autOn (T ⊓ L) (fsuUL T L I) ≤ autOn L (fsuUL T L I) := A4.autOn_mono inf_le_right
    have hQ2 : IsPGroup 2 Q' :=
      (isPGroup_autOn hsylTL.2.1).of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
    exact hQ2.comap_of_injective eρ.toMonoidHom eρ.injective
  have hPidx : ¬ 2 ∣ P.index := by
    rw [hPdef, Subgroup.index_comap_of_surjective Q' eρ.surjective, hQ']
    exact fun h => hsylTL.2.2 (h.trans (Subgroup.index_map_dvd _ (autOnHomOf_surjective hLU)))
  obtain ⟨g, hgP, hPg⟩ := exists_conj_unip hF hP2 hPidx
  have hPβ : ∀ p ∈ P, β (ρ p ⟨x, hxU⟩) = β ⟨x, hxU⟩ := by
    intro p hp
    have hp' : ((eρ p : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) ∈
        autOn (T ⊓ L) (fsuUL T L I) := hp
    obtain ⟨s, hsTL, hs⟩ := mem_autOn_iff'.mp hp'
    have hmem : ρ p ⟨x, hxU⟩ * (⟨x, hxU⟩ : ↥(fsuUL T L I))⁻¹ ∈ Ch10.cV1 T L I := by
      rw [Subgroup.mem_subgroupOf]
      have h1 : ((ρ p ⟨x, hxU⟩ : ↥(fsuUL T L I)) : G) = s * x * (s : G)⁻¹ := by
        show ((((eρ p : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I))
          ⟨x, hxU⟩ : ↥(fsuUL T L I)) : G) = _
        rw [← hs, coe_conjAct_apply']
      rw [Subgroup.coe_mul, Subgroup.coe_inv, h1]
      exact (hx s hsTL).2
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul]
    exact (hβk _).mpr hmem
  have hfix := fix_of_natural_conj hM ρ hZ β hβs hβk hρe g (hPβ _ (hPg 1))
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  set p := eρ.symm (autOnHomOf hLU ⟨s, hs.2⟩) with hpdef
  have hp : p ∈ P := by
    show eρ p ∈ Q'
    rw [hpdef, MulEquiv.apply_symm_apply, hQ']
    exact ⟨⟨s, hs.2⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
  obtain ⟨b, hb⟩ := hgP p hp
  have hp' : p = g⁻¹ * unipSL b * g := by rw [← hb]; group
  have h1 := hfix b
  rw [← hp'] at h1
  have h2 : ((ρ p ⟨x, hxU⟩ : ↥(fsuUL T L I)) : G) = s * x * s⁻¹ := by
    show ((((eρ p : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I))
      ⟨x, hxU⟩ : ↥(fsuUL T L I)) : G) = _
    rw [hpdef, MulEquiv.apply_symm_apply]
    exact autOnHomOf_apply hLU ⟨s, hs.2⟩ ⟨x, hxU⟩
  rw [h1] at h2
  calc s * x = s * x * s⁻¹ * s := by group
    _ = x * s := by rw [← h2]

end CFSG.Quasithin.Vol2.Ch10.SecA
