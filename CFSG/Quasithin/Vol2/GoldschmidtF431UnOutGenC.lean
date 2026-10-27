module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnOutGenB
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Basic

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13.F431

universe u v

section Main

variable {Mb : Type u} [Group Mb] [Finite Mb] {G : Type v} [Group G] [Finite G]
  {T Sb N N' V : Subgroup Mb} {f z t : Mb} {b : ↥N →* G} {b' : ↥N' →* G} {M M' : Subgroup G}

theorem UnGSetup.out_false [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (S : UnGSetup N N' b b' M M') (O : F431UnOut T Sb f N N' z t V) : False := by
  have hb := S.comp.inj₁
  have hfT := O.f_mem
  have hfN : f ∈ N := O.T_le hfT
  have hSyl : IsSylowTwoOf (subImg b T) ⊤ := S.sylow_img O
  have hTfN : spTf T f ≤ N := inf_le_left.trans O.T_le
  have hTfSyl : IsSylowTwoOf (subImg b (spTf T f))
      (Subgroup.centralizer ({b ⟨f, hfN⟩} : Set G)) := S.sylow_Tf O
  have hSN : Sb ≤ N := O.S_le.trans O.T_le
  obtain ⟨t₀, ht₀⟩ := O.cyc
  have ht₀T : t₀ ∈ T := by
    rw [ht₀]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t₀)
  have ht₀N : t₀ ∈ N := O.T_le ht₀T
  have hcyc : subImg b T = subImg b Sb ⊔ Subgroup.zpowers (b ⟨t₀, ht₀N⟩) := by
    conv_lhs => rw [ht₀]
    rw [subImg_sup hSN (Subgroup.zpowers_le.mpr ht₀N), subImg_zpowers ht₀N]
  refine CFSG.QuasithinUnique.Lin2.transfer_contradiction_cyclic hnab hSyl
    (subImg_mono b O.S_le) (subImg_le_normalizer b O.S_norm) hcyc
    (mem_subImg_of_mem b hfN hfT)
    (fun h => O.f_not ((mem_subImg_iff_of_injective hb hfN).mp h))
    ((sq_eq_one_iff_of_injective hb hfN).mpr O.f_sq) ?_
  intro g hg
  obtain ⟨s, hsN, hsS, hs⟩ := mem_subImg.mp hg
  have hf1 : f ≠ 1 := fun h => O.f_not (h ▸ Sb.one_mem)
  have hfg2 : b ⟨f, hfN⟩ ^ 2 = 1 := (sq_eq_one_iff_of_injective hb hfN).mpr O.f_sq
  have hs2 : s ^ 2 = 1 := by
    refine (sq_eq_one_iff_of_injective hb hsN).mp ?_
    rw [hs]
    calc (g⁻¹ * b ⟨f, hfN⟩ * g) ^ 2 = g⁻¹ * b ⟨f, hfN⟩ ^ 2 * g := by rw [sq, sq]; group
      _ = 1 := by rw [hfg2]; group
  have hs1 : s ≠ 1 := by
    rintro rfl
    have h1 : b ⟨1, hsN⟩ = 1 := map_one b
    rw [h1] at hs
    have : b ⟨f, hfN⟩ = 1 := by
      calc b ⟨f, hfN⟩ = g * (g⁻¹ * b ⟨f, hfN⟩ * g) * g⁻¹ := by group
        _ = 1 := by rw [← hs]; group
    exact hf1 (congrArg Subtype.val (hb (this.trans (map_one b).symm)))
  have hso : orderOf s = 2 := orderOf_eq_prime hs2 hs1
  obtain ⟨i, hi, -, hic⟩ := O.exists_rep S.comp hsS hso
  have hiN : i ∈ N := O.T_le (O.S_le (O.rep_mem hi))
  rw [amalgamMap_of_mem₁ b b' hsN, amalgamMap_of_mem₁ b b' hiN] at hic
  obtain ⟨c, hc⟩ := isConj_iff.mp hic.symm
  set u : G := b ⟨i, hiN⟩ with hu
  have hfu : (g * c) * u * (g * c)⁻¹ = b ⟨f, hfN⟩ := by
    calc (g * c) * u * (g * c)⁻¹ = g * (c * u * c⁻¹) * g⁻¹ := by group
      _ = g * b ⟨s, hsN⟩ * g⁻¹ := by rw [hc]
      _ = g * (g⁻¹ * b ⟨f, hfN⟩ * g) * g⁻¹ := by rw [hs]
      _ = b ⟨f, hfN⟩ := by group
  have hTg_le : subImg b (T ⊓ Subgroup.centralizer ({i} : Set Mb)) ≤
      Subgroup.centralizer ({u} : Set G) := by
    intro y hy
    obtain ⟨t, htN, ⟨htT, htC⟩, rfl⟩ := mem_subImg.mp hy
    show b ⟨t, htN⟩ ∈ Subgroup.centralizer ({u} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_iff_of_injective hb hiN htN).mpr (Subgroup.mem_centralizer_singleton_iff.mp htC)
  have hp : IsPGroup 2 (subImg b (T ⊓ Subgroup.centralizer ({i} : Set Mb))) :=
    hSyl.2.1.to_le (subImg_mono b inf_le_left)
  have h1 := card_le_twoPart hTg_le hp
  have h2 : twoPart (Subgroup.centralizer ({b ⟨f, hfN⟩} : Set G)) =
      twoPart (Subgroup.centralizer ({u} : Set G)) := by
    unfold twoPart
    rw [card_centralizer_eq_of_conj hfu]
  have h3 : Nat.card (subImg b (spTf T f)) =
      twoPart (Subgroup.centralizer ({b ⟨f, hfN⟩} : Set G)) := hTfSyl.card_eq
  have h4 : Nat.card (spTf T f) < Nat.card ↥(T ⊓ Subgroup.centralizer ({i} : Set Mb)) := by
    rcases hi with h | h
    · rw [h]
      exact O.Tf_lt_z
    · rw [h]
      exact O.Tf_lt_t
  rw [card_subImg hb (inf_le_left.trans O.T_le)] at h1
  rw [card_subImg hb hTfN] at h3
  omega

end Main

section Hyps

variable {G : Type} [Group G] {M1 M2 : Subgroup G} {D : Type} [Group D] {m f : ℕ}

theorem UnGSetup.of_hyps (hyps : F431Hyps M1 M2 .PSU m f) (E : LieExt D M1 M2) :
    UnGSetup E.Mb1 E.Mb2 E.b1 E.b2 M1 M2 :=
  ⟨E.comp, E.range_b1, E.range_b2, (hyps.2.2.2.1 (by simp)).1, (hyps.2.1 (Or.inr rfl)).2⟩

theorem UnGSetup.of_hyps_symm (hyps : F431Hyps M1 M2 .PSU m f) (E : LieExt D M1 M2) :
    UnGSetup E.Mb2 E.Mb1 E.b2 E.b1 M2 M1 :=
  ⟨⟨E.comp.inj₂, E.comp.inj₁, fun g h1 h2 => (E.comp.agree g h2 h1).symm⟩, E.range_b2,
    E.range_b1, (hyps.2.2.2.1 (by simp)).2, (hyps.2.1 (Or.inr rfl)).1⟩

end Hyps

theorem f431Out_of_unLie {m f : ℕ}
    (hfin : ∀ (D : Type) [Group D], LieModel D .PSU m 2 f → Finite D)
    (hLie : F431UnOutLieProp m f) : F431Out .PSU m f := by
  intro G _ _ hG hnab M1 M2 hyps D _ hD E
  by_contra hodd
  have : IsSimpleGroup G := hG
  have : Finite D := hfin D hD
  have : Finite (MulAut D) :=
    Finite.of_injective (fun φ : MulAut D => (φ : D → D)) fun _ _ h => MulEquiv.ext (congrFun h)
  have : Finite ↥E.K := inferInstance
  obtain ⟨T, Sb, g, z, t, V, O⟩ := hLie D hD E.toLieAmalgamExt hodd
  rcases O with O | O
  · exact UnGSetup.out_false hnab (UnGSetup.of_hyps hyps E) O
  · exact UnGSetup.out_false hnab (UnGSetup.of_hyps_symm hyps E) O

end CFSG.Quasithin.H13.F431.Un
