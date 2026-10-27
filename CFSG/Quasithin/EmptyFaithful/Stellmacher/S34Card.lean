module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34Sec2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv S42B1

namespace S34

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

open CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs
  (secData_secModule card_Zv_eq_sq comm_Zv_into)

omit [Finite G] in
theorem Cb_le_fixSecIn {δ : Geo H M} {A : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (Cb δ : Set G)) :
    Cb δ ≤ fixSecIn A (Cb δ) (Vn δ) := fun x hx =>
  Subgroup.subset_closure ⟨Cb_le_Vn δ hx, fun a ha => by
    have h1 := (Subgroup.mem_normalizer_iff.mp (hA ha) x).mp hx
    exact (Cb δ).mul_mem h1 ((Cb δ).inv_mem hx)⟩

theorem Zv_le_fixSecIn_edge (hG : Glob H M S) {δ μ : Geo H M} (hδ : vtype δ = false)
    (hμ : μ ∈ nbrs δ) : Zv μ ≤ fixSecIn (stab δ ⊓ stab μ) (Cb δ) (Vn δ) := by
  intro z hz
  have hzV : z ∈ Vn δ :=
    le_iSup₂_of_le (f := fun (ν : Geo H M) (_ : ν ∈ nbrs δ) => Zv ν) μ hμ le_rfl hz
  refine Subgroup.subset_closure ⟨hzV, fun t ht => ?_⟩
  by_cases htQ : t ∈ Qv μ
  · have h := Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hG.amalg μ hz).2 t htQ
    have e : t * z * t⁻¹ * z⁻¹ = 1 := by rw [h]; group
    rw [e]
    exact (Cb δ).one_mem
  · exact Zv_le_Cb hG hδ (comm_Zv_into hG.amalg hδ hμ (hG.central δ hδ) ⟨ht.2, ht.1⟩ htQ z hz)

theorem card_Zv_eq_two_of_good (hG : Glob H M S) {δ : Geo H M} (hδ : vtype δ = false)
    (hgood : Good δ) : Nat.card (Zv δ) = 2 := by
  obtain ⟨μ, hμ⟩ := exists_adj δ
  have hμ' : μ ∈ nbrs δ := hμ
  have hvμ : vtype μ = true := by
    have h := vtype_ne_of_adj hμ
    rw [hδ] at h
    generalize vtype μ = b at h ⊢
    cases b <;> simp_all
  obtain ⟨θ, hθ, hs, hk, hker, hPS, -⟩ := exists_vmodel hG hδ hμ'
  have hsn := hs.normal_subgroupOf
  have hD := secData_secModule hs θ hθ hk
  have hAK : stab δ ⊓ stab μ ≤ stab δ := inf_le_left
  set F := fixSecIn (stab δ ⊓ stab μ) (Cb δ) (Vn δ) with hF
  have h1 : F.relIndex (Vn δ) = (fixW (secModule hs θ hθ hk) S5Syl).index := by
    rw [hF, hD.relIndex_fixSecIn hs.le hAK, hPS]
  have h2 : (Cb δ).relIndex (Vn δ) = Nat.card (secModule hs θ hθ hk).W := hD.relIndex_eq
  have hCF : Cb δ ≤ F := Cb_le_fixSecIn (fun a ha => hs.normL (hAK ha))
  have hFV : F ≤ Vn δ := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hx, -⟩
    exact hx
  have h3 : Nat.card (fixW (secModule hs θ hθ hk) S5Syl) = 2 := by
    have key : ∀ {Mo : Model 5}, Mo = orth ∨ Mo = nat →
        (secModule hs θ hθ hk).Iso Mo → Nat.card (fixW (secModule hs θ hθ hk) S5Syl) = 2 := by
      intro Mo hMo e
      have hp := congrArg (fun p => p.2.1) (profile_sylow Mo hMo card_S5Syl)
      simp only [profile] at hp
      rw [e.fixW_eq, Subgroup.card_map_of_injective e.toMulEquiv.injective] at hp
      exact hp
    obtain ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ := (good_iff_iso hG hδ hθ hs hk hker).mp hgood
    · exact key (Or.inl rfl) e
    · exact key (Or.inr rfl) e
  have hFC : (Cb δ).relIndex F = 2 := by
    have hmul := Subgroup.relIndex_mul_relIndex (Cb δ) F (Vn δ) hCF hFV
    have hpos : 0 < (fixW (secModule hs θ hθ hk) S5Syl).index :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hc := Subgroup.card_mul_index (fixW (secModule hs θ hθ hk) S5Syl)
    rw [h1, h2, ← hc, h3] at hmul
    rw [mul_comm 2] at hmul
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_comm]; exact hmul)
  have hZF : Zv μ ≤ F := Zv_le_fixSecIn_edge hG hδ hμ'
  have hle : (Cb δ).relIndex (Zv μ) ≤ 2 := by
    rw [← hFC]
    exact Subgroup.relIndex_le_of_le_right hZF Subgroup.index_ne_zero_of_finite
  have hZC : Cb δ ⊓ Zv μ = Zv δ := Cb_inf_Zv_eq hG hδ hμ'
  have hsq := card_Zv_eq_sq hG.amalg hvμ hμ.symm (hG.central δ hδ)
  have hdiv : (Cb δ).relIndex (Zv μ) * Nat.card (Zv δ) = Nat.card (Zv μ) := by
    have h := Subgroup.relIndex_mul_card (Cb δ) (Zv μ)
    rwa [hZC] at h
  have hpos : 0 < Nat.card (Zv δ) := Nat.card_pos
  have hne : Nat.card (Zv δ) ≠ 1 := fun h =>
    Zv_ne_bot hG.amalg δ (Subgroup.card_eq_one.mp h)
  rw [hsq, pow_two] at hdiv
  have hidx : (Cb δ).relIndex (Zv μ) = Nat.card (Zv δ) :=
    Nat.eq_of_mul_eq_mul_right hpos hdiv
  omega

end S34

end F53.Stellmacher

end CFSG.Quasithin
