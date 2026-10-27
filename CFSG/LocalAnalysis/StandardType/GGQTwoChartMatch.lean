module

public import CFSG.LocalAnalysis.StandardType.GGQTwoChartDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartMatchModel
import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofRefl
import CFSG.LocalAnalysis.StandardType.GGTypeAReflOverEmb

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan CFSG.Open
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open scoped Pointwise Matrix

variable {G : Type} [Group G] [Finite G]
variable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {m n : ℕ}

section Helpers

variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
variable {ψ : Su F0 2 1 m →* G}

theorem qTwoChartMatch_map_diag_le (hF0 : Nat.card F0 = 4)
    (hψ : QTwoOrdModel Bs L ψ) (hBs : GGBstar 3 B Bs) :
    (qTwoLMDivKind_diag F0 m).map ψ ≤ Bs := by
  rintro _ ⟨t, ht, rfl⟩
  refine hBs.2.2.2 (ψ t) ?_ ?_
  · rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨g, hgdiag, hu'⟩ := hψ.2.2 ⟨b, hb⟩
    obtain ⟨u', hu'eq, hu'ψ⟩ := hu' t
    have hcomm : g * (t : GL (Fin m) F0) = (t : GL (Fin m) F0) * g :=
      qTwoChartMatch_diag_commute hgdiag ht
    have hcoe : (u' : GL (Fin m) F0) = (t : GL (Fin m) F0) := by
      rw [hu'eq, hcomm]
      group
    have hut : u' = t := Subtype.ext hcoe
    rw [hut] at hu'ψ
    have hb' : ψ t * b = b * ψ t := by
      calc ψ t * b = (b * ψ t * b⁻¹) * b := by
            conv_lhs => rw [hu'ψ]
        _ = b * ψ t := by group
    exact hb'.symm
  · rw [← map_pow, qTwoLMDivKind_pow_three_of_mem_diag hF0 ht, map_one]

theorem qTwoChartMatch_exists_conj_eq (hψ : QTwoOrdModel Bs L ψ)
    (σ : Equiv.Perm (Fin m)) (b : ↥Bs) :
    ∃ g : GL (Fin m) F0, ggIsDiagMat g ∧ ∃ d : Su F0 2 1 m,
      (d : GL (Fin m) F0) = (qTwoChartMatch_permHom (F0 := F0) σ : GL (Fin m) F0) * g *
        (qTwoChartMatch_permHom (F0 := F0) σ : GL (Fin m) F0)⁻¹ * g⁻¹ ∧
      ψ (qTwoChartMatch_permHom (F0 := F0) σ) * (b : G) *
          (ψ (qTwoChartMatch_permHom (F0 := F0) σ))⁻¹ = ψ d * (b : G) := by
  obtain ⟨g, hg, hu⟩ := hψ.2.2 b
  obtain ⟨u', hu'e, hu'ψ⟩ := hu ((qTwoChartMatch_permHom (F0 := F0) σ)⁻¹)
  refine ⟨g, hg, qTwoChartMatch_permHom (F0 := F0) σ * u', ?_, ?_⟩
  · rw [Subgroup.coe_mul, hu'e, Subgroup.coe_inv]
    group
  · rw [map_mul, hu'ψ, map_inv]
    group

theorem qTwoChartMatch_conj_mem (hF0 : Nat.card F0 = 4)
    (hψ : QTwoOrdModel Bs L ψ) (hBs : GGBstar 3 B Bs)
    (σ : Equiv.Perm (Fin m)) (b : ↥Bs) :
    ψ (qTwoChartMatch_permHom (F0 := F0) σ) * (b : G) *
        (ψ (qTwoChartMatch_permHom (F0 := F0) σ))⁻¹ ∈ Bs := by
  obtain ⟨g, hg, d, hdcoe, hdψ⟩ := qTwoChartMatch_exists_conj_eq (F0 := F0) hψ σ b
  have hdT : d ∈ qTwoLMDivKind_diag F0 m := by
    show ggIsDiagMat (d : GL (Fin m) F0)
    rw [hdcoe]
    exact qTwoChartMatch_isDiag_commutator (F0 := F0) σ hg
  have hdBs : ψ d ∈ Bs :=
    qTwoChartMatch_map_diag_le (F0 := F0) hF0 hψ hBs (Subgroup.mem_map_of_mem ψ hdT)
  rw [hdψ]
  exact Bs.mul_mem hdBs b.2

theorem qTwoChartMatch_mem_normalizer (hF0 : Nat.card F0 = 4)
    (hψ : QTwoOrdModel Bs L ψ) (hBs : GGBstar 3 B Bs) (σ : Equiv.Perm (Fin m)) :
    ψ (qTwoChartMatch_permHom (F0 := F0) σ) ∈ Subgroup.normalizer (Bs : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    exact qTwoChartMatch_conj_mem (F0 := F0) hF0 hψ hBs σ ⟨b, hb⟩
  · intro hb
    have h1 : qTwoChartMatch_permHom (F0 := F0) σ⁻¹ =
        (qTwoChartMatch_permHom (F0 := F0) σ)⁻¹ := map_inv _ σ
    have h2 : ψ (qTwoChartMatch_permHom (F0 := F0) σ⁻¹) =
        (ψ (qTwoChartMatch_permHom (F0 := F0) σ))⁻¹ := by
      rw [h1, map_inv]
    have h3 := qTwoChartMatch_conj_mem (F0 := F0) hF0 hψ hBs σ⁻¹
      ⟨ψ (qTwoChartMatch_permHom (F0 := F0) σ) * b *
        (ψ (qTwoChartMatch_permHom (F0 := F0) σ))⁻¹, hb⟩
    rw [h2, inv_inv] at h3
    have h4 : (ψ (qTwoChartMatch_permHom (F0 := F0) σ))⁻¹ *
        (ψ (qTwoChartMatch_permHom (F0 := F0) σ) * b *
          (ψ (qTwoChartMatch_permHom (F0 := F0) σ))⁻¹) *
          (ψ (qTwoChartMatch_permHom (F0 := F0) σ)) = b := by
      group
    rwa [h4] at h3

noncomputable def qTwoChartMatch_conjHom (hF0 : Nat.card F0 = 4)
    (hψ : QTwoOrdModel Bs L ψ) (hBs : GGBstar 3 B Bs) :
    Equiv.Perm (Fin m) →* MulAut ↥Bs :=
  Bs.normalizerMonoidHom.comp
    ((ψ.comp (qTwoChartMatch_permHom (F0 := F0))).codRestrict
      (Subgroup.normalizer (Bs : Set G))
      (fun σ => qTwoChartMatch_mem_normalizer (F0 := F0) hF0 hψ hBs σ))

@[simp]
theorem qTwoChartMatch_conjHom_apply (hF0 : Nat.card F0 = 4)
    (hψ : QTwoOrdModel Bs L ψ) (hBs : GGBstar 3 B Bs) (σ : Equiv.Perm (Fin m))
    (b : ↥Bs) :
    (((qTwoChartMatch_conjHom (F0 := F0) hF0 hψ hBs σ) b : ↥Bs) : G) =
      ψ (qTwoChartMatch_permHom (F0 := F0) σ) * (b : G) *
        (ψ (qTwoChartMatch_permHom (F0 := F0) σ))⁻¹ := by
  unfold qTwoChartMatch_conjHom
  simp only [MonoidHom.comp_apply, MonoidHom.codRestrict_apply]
  exact Subgroup.normalizerMonoidHom_apply_apply_coe Bs _ b

theorem qTwoChartMatch_conjHom_normalizer (hF0 : Nat.card F0 = 4)
    (hψ : QTwoOrdModel Bs L ψ) (hBs : GGBstar 3 B Bs) (σ : Equiv.Perm (Fin m)) :
    Bs.normalizerMonoidHom
        ⟨ψ (qTwoChartMatch_permHom (F0 := F0) σ),
          qTwoChartMatch_mem_normalizer (F0 := F0) hF0 hψ hBs σ⟩ =
      qTwoChartMatch_conjHom (F0 := F0) hF0 hψ hBs σ := by
  unfold qTwoChartMatch_conjHom
  rw [MonoidHom.comp_apply]
  congr 1

theorem qTwoChartMatch_conjHom_injective (hF0 : Nat.card F0 = 4)
    (hψ : QTwoOrdModel Bs L ψ) (hBs : GGBstar 3 B Bs) (hm : 5 ≤ m) :
    Function.Injective (qTwoChartMatch_conjHom (F0 := F0) hF0 hψ hBs) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  by_contra hne
  obtain ⟨t, ht, hcenter⟩ :=
    qTwoChartMatch_exists_diag_not_mem_center (F0 := F0) hF0 hm hne
  have hmem : ψ t ∈ Bs :=
    qTwoChartMatch_map_diag_le (F0 := F0) hF0 hψ hBs (Subgroup.mem_map_of_mem ψ ht)
  have hfix : qTwoChartMatch_conjHom (F0 := F0) hF0 hψ hBs σ ⟨ψ t, hmem⟩ =
      ⟨ψ t, hmem⟩ := by
    rw [hσ]
    rfl
  have happ := qTwoChartMatch_conjHom_apply (F0 := F0) hF0 hψ hBs σ ⟨ψ t, hmem⟩
  rw [hfix] at happ
  have happ' : ψ t = ψ (qTwoChartMatch_permHom (F0 := F0) σ) * ψ t *
      (ψ (qTwoChartMatch_permHom (F0 := F0) σ))⁻¹ := by
    simpa using happ
  have hker : qTwoChartMatch_permHom (F0 := F0) σ * t *
      (qTwoChartMatch_permHom (F0 := F0) σ)⁻¹ * t⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [← happ']
    group
  exact hcenter (hψ.2.1 hker)

@[expose]
noncomputable def qTwoChartMatch_conjDelta (hF0 : Nat.card F0 = 4)
    (hψ : QTwoOrdModel Bs L ψ) (hBs : GGBstar 3 B Bs) (hE : IsElemAbelian 3 Bs)
    (σ : Equiv.Perm (Fin m)) : ↥Bs →* ↥Bs :=
  MonoidHom.mk' (fun b => qTwoChartMatch_conjHom (F0 := F0) hF0 hψ hBs σ b * b⁻¹)
    (fun a b => by
      letI : CommGroup ↥Bs := { (inferInstance : Group ↥Bs) with
        mul_comm := fun a b => hE.1.is_comm.comm a b }
      rw [map_mul, mul_inv_rev]
      ac_rfl)

@[simp]
theorem qTwoChartMatch_conjDelta_apply (hF0 : Nat.card F0 = 4)
    (hψ : QTwoOrdModel Bs L ψ) (hBs : GGBstar 3 B Bs) (hE : IsElemAbelian 3 Bs)
    (σ : Equiv.Perm (Fin m)) (b : ↥Bs) :
    qTwoChartMatch_conjDelta (F0 := F0) hF0 hψ hBs hE σ b =
      qTwoChartMatch_conjHom (F0 := F0) hF0 hψ hBs σ b * b⁻¹ := rfl

theorem qTwoChartMatch_conjDelta_fixed_card (hF0 : Nat.card F0 = 4)
    (hψ : QTwoOrdModel Bs L ψ) (hBs : GGBstar 3 B Bs) (hE : IsElemAbelian 3 Bs)
    (σ : Equiv.Perm (Fin m)) :
    Nat.card {b : ↥Bs // qTwoChartMatch_conjHom (F0 := F0) hF0 hψ hBs σ b = b} =
      Nat.card ↥(qTwoChartMatch_conjDelta (F0 := F0) hF0 hψ hBs hE σ).ker := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun b => ?_)
  rw [MonoidHom.mem_ker, qTwoChartMatch_conjDelta_apply]
  exact mul_inv_eq_one.symm

theorem qTwoChartMatch_conjDelta_range_le_three (hF0 : Nat.card F0 = 4)
    (hψ : QTwoOrdModel Bs L ψ) (hBs : GGBstar 3 B Bs) (hE : IsElemAbelian 3 Bs)
    {i j : Fin m} (hij : i ≠ j) :
    Nat.card ↥(qTwoChartMatch_conjDelta (F0 := F0) hF0 hψ hBs hE
      (Equiv.swap i j)).range ≤ 3 := by
  classical
  obtain ⟨S, hScard, hS⟩ :=
    qTwoChartMatch_exists_finset_swap_commutator (F0 := F0) hF0 hij
  let δ := qTwoChartMatch_conjDelta (F0 := F0) hF0 hψ hBs hE (Equiv.swap i j)
  have hex : ∀ x : ↥δ.range, ∃ d ∈ S, ψ d = (x : ↥Bs) := by
    rintro ⟨x, hx⟩
    rw [MonoidHom.mem_range] at hx
    obtain ⟨b, hb⟩ := hx
    obtain ⟨g, hg, d, hdcoe, hdψ⟩ :=
      qTwoChartMatch_exists_conj_eq (F0 := F0) hψ (Equiv.swap i j) b
    have hdT : d ∈ qTwoLMDivKind_diag F0 m := by
      show ggIsDiagMat (d : GL (Fin m) F0)
      rw [hdcoe]
      exact qTwoChartMatch_isDiag_commutator (F0 := F0) (Equiv.swap i j) hg
    have hdBs : ψ d ∈ Bs :=
      qTwoChartMatch_map_diag_le (F0 := F0) hF0 hψ hBs (Subgroup.mem_map_of_mem ψ hdT)
    have hφb := qTwoChartMatch_conjHom_apply (F0 := F0) hF0 hψ hBs (Equiv.swap i j) b
    have hxG : (x : G) = ψ d := by
      have h1 : (x : G) = ((qTwoChartMatch_conjHom (F0 := F0) hF0 hψ hBs
          (Equiv.swap i j) b : ↥Bs) : G) * (b : G)⁻¹ := by
        have hb' := congrArg Subtype.val hb
        rw [qTwoChartMatch_conjDelta_apply] at hb'
        simpa using hb'.symm
      rw [h1, hφb, hdψ]
      group
    exact ⟨d, hS g hg d hdcoe, hxG.symm⟩
  let f : ↥δ.range → S := fun x =>
    ⟨Classical.choose (hex x), (Classical.choose_spec (hex x)).1⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hxspec := (Classical.choose_spec (hex x)).2
    have hyspec := (Classical.choose_spec (hex y)).2
    have hval : Classical.choose (hex x) = Classical.choose (hex y) :=
      congrArg Subtype.val hxy
    apply Subtype.ext
    apply Subtype.ext
    rw [← hxspec, ← hyspec]
    exact congrArg ψ hval
  calc Nat.card ↥δ.range ≤ Nat.card S := Nat.card_le_card_of_injective f hf
    _ = S.card := Nat.card_eq_finsetCard S
    _ ≤ 3 := hScard

theorem qTwoChartMatch_isReflection_swap (hF0 : Nat.card F0 = 4)
    (hψ : QTwoOrdModel Bs L ψ) (hBs : GGBstar 3 B Bs)
    (hm : 5 ≤ m) (hcard : Nat.card ↥Bs = 3 ^ m) (hE : IsElemAbelian 3 Bs)
    {i j : Fin m} (hij : i ≠ j) :
    GGIsReflection 3 (qTwoChartMatch_conjHom (F0 := F0) hF0 hψ hBs (Equiv.swap i j)) := by
  classical
  let φ := qTwoChartMatch_conjHom (F0 := F0) hF0 hψ hBs (Equiv.swap i j)
  let δ := qTwoChartMatch_conjDelta (F0 := F0) hF0 hψ hBs hE (Equiv.swap i j)
  have hφ2 : φ ^ 2 = 1 := by
    rw [← map_pow, show (Equiv.swap i j) ^ 2 = 1 by rw [sq, Equiv.swap_mul_self], map_one]
  have hcardmul : Nat.card ↥δ.ker * Nat.card ↥δ.range = Nat.card ↥Bs := by
    have h1 := Subgroup.card_mul_index δ.ker
    rwa [Subgroup.index_ker] at h1
  have hdvd : Nat.card ↥δ.range ∣ 3 ^ m := by
    rw [← hcard]
    exact ⟨Nat.card ↥δ.ker, by rw [mul_comm, hcardmul]⟩
  have hpos : 0 < Nat.card ↥δ.range := by
    have : Nonempty ↥δ.range :=
      ⟨⟨1, MonoidHom.mem_range.mpr ⟨1, map_one δ⟩⟩⟩
    exact Nat.card_pos
  have h2 : Nat.card ↥δ.range ≠ 2 := by
    intro h
    rw [h] at hdvd
    have h23 : 2 ∣ 3 := Nat.prime_two.dvd_of_dvd_pow hdvd
    norm_num at h23
  have h1 : Nat.card ↥δ.range ≠ 1 := by
    intro h
    have hbot : δ.range = ⊥ := (Subgroup.eq_bot_iff_card (H := δ.range)).mpr h
    have hφ1 : φ = 1 := by
      refine MulEquiv.ext fun b => ?_
      have hb : qTwoChartMatch_conjHom (F0 := F0) hF0 hψ hBs (Equiv.swap i j) b * b⁻¹ = 1 := by
        have hmem : δ b ∈ (⊥ : Subgroup ↥Bs) := by
          rw [← hbot]
          exact MonoidHom.mem_range.mpr ⟨b, rfl⟩
        simpa [δ] using hmem
      have hb' := mul_inv_eq_one.mp hb
      simpa [φ] using hb'
    have hφeq : qTwoChartMatch_conjHom (F0 := F0) hF0 hψ hBs (Equiv.swap i j) = 1 := by
      simpa [φ] using hφ1
    have hσ : Equiv.swap i j = 1 :=
      qTwoChartMatch_conjHom_injective (F0 := F0) hF0 hψ hBs hm
        (by rw [hφeq, map_one])
    exact hij (Equiv.swap_eq_refl_iff.mp hσ)
  have hle : Nat.card ↥δ.range ≤ 3 :=
    qTwoChartMatch_conjDelta_range_le_three (F0 := F0) hF0 hψ hBs hE hij
  have hrange : Nat.card ↥δ.range = 3 := by omega
  refine ⟨hφ2, ?_⟩
  rw [qTwoChartMatch_conjDelta_fixed_card (F0 := F0) hF0 hψ hBs hE (Equiv.swap i j)]
  rw [hrange] at hcardmul
  exact hcardmul

theorem qTwoChartMatch_conjHom_mem (hF0 : Nat.card F0 = 4)
    (hψ : QTwoOrdModel Bs L ψ) (hBs : GGBstar 3 B Bs) (σ : Equiv.Perm (Fin m)) :
    qTwoChartMatch_conjHom (F0 := F0) hF0 hψ hBs σ ∈ ggAutomizerJoin L Bs 𝒦 := by
  refine Subgroup.mem_sup_left (Subgroup.subset_closure ?_)
  rw [mem_ggInduced_iff]
  have hψ' : QTwoOrdModel Bs ψ.range ψ := hψ.1.symm ▸ hψ
  refine ⟨⟨ψ (qTwoChartMatch_permHom (F0 := F0) σ),
    qTwoChartMatch_mem_normalizer (F0 := F0) (L := ψ.range) hF0 hψ' hBs σ⟩, ?_, ?_⟩
  · exact hψ.1 ▸ MonoidHom.mem_range.mpr ⟨_, rfl⟩
  · exact qTwoChartMatch_conjHom_normalizer (F0 := F0) hF0 hψ hBs σ

end Helpers

theorem qTwoChartMatch_liftsPerm (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] (hF0 : Nat.card F0 = 4)
    (ψ : Su F0 2 1 m →* G) (hψ : QTwoOrdModel Bs L ψ) (hBs : GGBstar 3 B Bs)
    (φ : Equiv.Perm (Fin m) →* Equiv.Perm (Fin (n + 1)))
    (hcφ : ∀ σ, ((S.ρA (φ σ) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
      qTwoChartMatch_conjHom (F0 := F0) hF0 hψ hBs σ)
    (σ : Equiv.Perm (Fin m)) :
    QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA
      (ψ (qTwoChartMatch_permHom (F0 := F0) σ)) (φ σ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Subgroup.mem_sup_left (hψ.1 ▸ MonoidHom.mem_range.mpr ⟨_, rfl⟩)
  · have hψ' : QTwoOrdModel Bs ψ.range ψ := hψ.1.symm ▸ hψ
    exact qTwoChartMatch_mem_normalizer (F0 := F0) (L := ψ.range) hF0 hψ' hBs σ
  · intro b
    rw [hcφ σ]
    exact qTwoChartMatch_conjHom_apply (F0 := F0) hF0 hψ hBs σ b

open Classical in
theorem qTwoChartMatch_extendDomain_eq {m n : ℕ}
    {φ : Equiv.Perm (Fin m) →* Equiv.Perm (Fin (n + 1))}
    (ε0 : Fin m ↪ Fin (n + 1))
    (hι_apply : ∀ σ a, φ σ (ε0 a) = ε0 (σ a))
    (hι_fix : ∀ σ w, w ∉ Set.range ε0 → φ σ w = w)
    (σ : Equiv.Perm (Fin m)) :
    σ.extendDomain (Equiv.ofInjective ε0 ε0.injective) = φ σ := by
  refine Equiv.ext fun b => ?_
  by_cases hb : b ∈ Set.range ε0
  · obtain ⟨a, rfl⟩ := hb
    have hb' : ε0 a ∈ Set.range ε0 := ⟨a, rfl⟩
    rw [Equiv.Perm.extendDomain_apply_subtype (e := σ)
      (f := Equiv.ofInjective ε0 ε0.injective) hb']
    have hsymm : (Equiv.ofInjective ε0 ε0.injective).symm ⟨ε0 a, hb'⟩ = a := by
      simpa using Equiv.ofInjective_symm_apply (f := (ε0 : Fin m → Fin (n + 1)))
        ε0.injective a
    rw [hsymm]
    exact (hι_apply σ a).symm
  · rw [Equiv.Perm.extendDomain_apply_not_subtype (e := σ)
      (f := Equiv.ofInjective ε0 ε0.injective) hb]
    exact (hι_fix σ b hb).symm

open Classical in
theorem qTwoChartMatch_frameMatch_of (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    (ψ : Su F0 2 1 m →* G)
    (φ : Equiv.Perm (Fin m) →* Equiv.Perm (Fin (n + 1)))
    (ε0 : Fin m ↪ Fin (n + 1))
    (hh : ∀ σ, QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA
      (ψ (qTwoChartMatch_permHom (F0 := F0) σ)) (φ σ))
    (hπ : ∀ σ, σ.extendDomain (Equiv.ofInjective ε0 ε0.injective) = φ σ) :
    QTwoFrameMatch S ψ ε0 := by
  intro σ
  refine ⟨qTwoChartMatch_permHom (F0 := F0) σ,
    qTwoChartMatch_permHom_mulVec (F0 := F0) σ, ?_⟩
  rw [hπ σ]
  exact hh σ

theorem qTwoChart_frameMatching (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] (hF0 : Nat.card F0 = 4)
    (ψ : Su F0 2 1 m →* G) (hψ : QTwoOrdModel Bs L ψ) :
    ∃ ε0 : Fin m ↪ Fin (n + 1), QTwoFrameMatch S ψ ε0 := by
  classical
  have hBs : GGBstar 3 B Bs := S.hcfg.1.1.2.1
  have hm5 : 5 ≤ m := S.hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  let c : Equiv.Perm (Fin (k + 1)) →* MulAut ↥Bs :=
    qTwoChartMatch_conjHom (F0 := F0) hF0 hψ hBs
  have hc_inj : Function.Injective c :=
    qTwoChartMatch_conjHom_injective (F0 := F0) hF0 hψ hBs S.hm
  have hc_refl : ∀ a b : Fin (k + 1), a ≠ b →
      GGIsReflection 3 (c (Equiv.swap a b)) :=
    fun a b hab => qTwoChartMatch_isReflection_swap (F0 := F0) hF0 hψ hBs S.hm
      S.hLocal.card S.hLocal.elemAb hab
  let c' : Equiv.Perm (Fin (k + 1)) →* ↥(ggAutomizerJoin L Bs 𝒦) :=
    c.codRestrict (ggAutomizerJoin L Bs 𝒦)
      (fun σ => qTwoChartMatch_conjHom_mem (F0 := F0) hF0 hψ hBs σ)
  let φ : Equiv.Perm (Fin (k + 1)) →* Equiv.Perm (Fin (n + 1)) :=
    S.ρA.symm.toMonoidHom.comp c'
  have hφ_inj : Function.Injective φ := by
    intro σ τ hστ
    apply hc_inj
    have h1 : c' σ = c' τ := by
      have h := congrArg S.ρA hστ
      simpa [φ] using h
    exact congrArg Subtype.val h1
  have hsw : ∀ a b : Fin (k + 1), a ≠ b → (φ (Equiv.swap a b)).IsSwap := by
    intro a b hab
    let E : Equiv.Perm (Fin (n + 1)) →* MulAut ↥Bs :=
      (ggAutomizerJoin L Bs 𝒦).subtype.comp S.ρA.toMonoidHom
    have hEφ : E (φ (Equiv.swap a b)) = c (Equiv.swap a b) := by
      simp [E, φ, c']
    have hinjE : Function.Injective E := by
      intro x y hxy
      exact S.ρA.injective (Subtype.val_injective hxy)
    have h := isSwap_of_ggIsReflection (p := 3) (Bs := Bs) (by norm_num)
      S.hLocal.elemAb E hinjE (fun x y hxy => S.hrefl x y hxy)
      (π := φ (Equiv.swap a b)) (by rw [hEφ]; exact hc_refl a b hab)
    exact h
  obtain ⟨ι, hι_inj, hι_apply, hι_fix⟩ :=
    TypeAReflOver.exists_embedding_of_isSwap (n := k) (β := Fin (n + 1)) (by omega)
      φ hφ_inj hsw
  let ε0 : Fin (k + 1) ↪ Fin (n + 1) := ⟨ι, hι_inj⟩
  refine ⟨ε0, ?_⟩
  have hcφ : ∀ τ, ((S.ρA (φ τ) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
      qTwoChartMatch_conjHom (F0 := F0) hF0 hψ hBs τ := by
    intro τ
    simp [φ, c', c]
  exact qTwoChartMatch_frameMatch_of S ψ φ ε0
    (fun σ => qTwoChartMatch_liftsPerm S hF0 ψ hψ hBs φ hcφ σ)
    (fun σ => qTwoChartMatch_extendDomain_eq ε0 hι_apply hι_fix σ)

end CFSG.StandardType.QTwo

end
