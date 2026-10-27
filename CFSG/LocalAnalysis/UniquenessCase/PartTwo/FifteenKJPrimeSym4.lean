module

public import CFSG.Quasithin.Background.B5FinPerm
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private abbrev s15k_jp_sym4_good (σ : Equiv.Perm (Fin 4)) : Prop :=
  ∀ m : G6.PermMod 4, m ∈ G6.coreMod 4 →
    m⁻¹ * G6.permAct 4 σ m = 1 ∨ m⁻¹ * G6.permAct 4 σ m = G6.allOnes 4

theorem s15k_jp_sym4_card {W : Type} [CommGroup W] {J : Subgroup (MulAut W)} {R : Subgroup W}
    (h : SymmetricNatural J R ⊥ 4)
    (hfaith : ∀ j ∈ J, (∀ r ∈ R, j r = r) → j = 1) : Nat.card J = 6 ∧ Nat.card R = 4 := by
  unfold SymmetricNatural at h
  unfold FFModel.Realizes at h
  obtain ⟨π, hπ⟩ := h
  unfold FFModel.RealizesVia at hπ
  simp only [FFModel.symDn] at hπ
  obtain ⟨hπs, hZU, hker, hUinv, hZinv, hsec, hkerinv, β, hβs, hβk, hβe⟩ := hπ
  let β' : ↥R →* ↥(G6.coreMod 4) ⧸
      (Subgroup.zpowers (G6.allOnes 4) ⊓ G6.coreMod 4).subgroupOf (G6.coreMod 4) := β
  let π' : Equiv.Perm (Fin 4) →* ↥J := π
  have hπ's : Function.Surjective π' := fun y => hπs y
  have hβ's : Function.Surjective (⇑β') := fun y => hβs y
  have hβk' : ∀ u : ↥R, (⇑β') u = 1 ↔ (u : W) ∈ (⊥ : Subgroup W) := fun u => hβk u
  have hβinj : Function.Injective (⇑β') := by
    intro u v huv
    have h1 : (⇑β') (u * v⁻¹) = 1 := by
      rw [map_mul, map_inv, huv, mul_inv_cancel]
    have h2 : (u * v⁻¹ : W) ∈ (⊥ : Subgroup W) := (hβk' (u * v⁻¹)).mp h1
    have h3 : u * v⁻¹ = 1 := Subtype.ext (Subgroup.mem_bot.mp h2)
    have h4 : u = v := by
      have := congrArg (fun x : ↥R => x * v) h3
      simpa [mul_assoc] using this
    exact h4
  have hβsurj : Function.Surjective (⇑β') := fun y => hβ's y
  have hsec8 : Nat.card ↥(G6.coreMod 4) = 8 := by
    show Nat.card {x : G6.PermMod 4 // ∑ i, Multiplicative.toAdd x i = 0} = 8
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hones_mem : G6.allOnes 4 ∈ G6.coreMod 4 := by
    rw [G6.mem_coreMod]
    decide +kernel
  have hzp_le : Subgroup.zpowers (G6.allOnes 4) ≤ G6.coreMod 4 :=
    Subgroup.zpowers_le.mpr hones_mem
  have hker_eq : Subgroup.zpowers (G6.allOnes 4) ⊓ G6.coreMod 4 =
      Subgroup.zpowers (G6.allOnes 4) := by
    apply le_antisymm
    · exact inf_le_left
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨hx, hzp_le hx⟩
  have hord : orderOf (G6.allOnes 4) = 2 := by
    have hsq : G6.allOnes 4 * G6.allOnes 4 = 1 := B5FinPerm.allOnes_mul_self 4
    have hne : G6.allOnes 4 ≠ 1 := by decide +kernel
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hsq) hne
  have hker2 : Nat.card ↥((Subgroup.zpowers (G6.allOnes 4) ⊓ G6.coreMod 4).subgroupOf
      (G6.coreMod 4)) = 2 := by
    rw [hker_eq]
    calc Nat.card ↥((Subgroup.zpowers (G6.allOnes 4)).subgroupOf (G6.coreMod 4))
        = Nat.card ↥(Subgroup.zpowers (G6.allOnes 4)) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzp_le).toEquiv
      _ = orderOf (G6.allOnes 4) := Nat.card_zpowers (G6.allOnes 4)
      _ = 2 := hord
  have hcardquot : Nat.card (↥(G6.coreMod 4) ⧸
      (Subgroup.zpowers (G6.allOnes 4) ⊓ G6.coreMod 4).subgroupOf (G6.coreMod 4)) = 4 := by
    have hcard2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((Subgroup.zpowers (G6.allOnes 4) ⊓ G6.coreMod 4).subgroupOf (G6.coreMod 4))
    rw [hsec8, hker2] at hcard2
    omega
  have hR4 : Nat.card R = 4 := by
    calc Nat.card R = Nat.card (↥(G6.coreMod 4) ⧸
          (Subgroup.zpowers (G6.allOnes 4) ⊓ G6.coreMod 4).subgroupOf (G6.coreMod 4)) :=
          Nat.card_congr (Equiv.ofBijective (⇑β') ⟨hβinj, hβsurj⟩)
      _ = 4 := hcardquot
  have hP : ∀ σ : Equiv.Perm (Fin 4), σ ∈ π'.ker ↔ s15k_jp_sym4_good σ := by
    intro σ
    constructor
    · intro hσ m hm
      have hσ1 : π' σ = 1 := MonoidHom.mem_ker.mp hσ
      have hcoe : ((π' σ : ↥J) : MulAut W) = 1 := by rw [hσ1]; rfl
      obtain ⟨u, hu⟩ := hβ's (QuotientGroup.mk (⟨m, hm⟩ : ↥(G6.coreMod 4)))
      have hu' : ((π' σ : ↥J) : MulAut W) (u : W) ∈ R := hUinv (π' σ) u u.2
      have hm' : G6.permAct 4 σ m ∈ G6.coreMod 4 := hsec σ m hm
      have hsub : (⟨((π' σ : ↥J) : MulAut W) (u : W), hu'⟩ : ↥R) = u := by
        apply Subtype.ext
        change ((π' σ : ↥J) : MulAut W) (u : W) = (u : W)
        rw [hcoe]
        rfl
      have key : β' u = QuotientGroup.mk
          (⟨G6.permAct 4 σ m, hm'⟩ : ↥(G6.coreMod 4)) := by
        rw [← hsub]
        exact hβe σ u ⟨m, hm⟩ hu' hm' hu
      have heq : QuotientGroup.mk (⟨m, hm⟩ : ↥(G6.coreMod 4)) =
          QuotientGroup.mk (⟨G6.permAct 4 σ m, hm'⟩ : ↥(G6.coreMod 4)) :=
        hu.symm.trans key
      have hmem := QuotientGroup.eq.mp heq
      have hk0 : m⁻¹ * G6.permAct 4 σ m ∈
          Subgroup.zpowers (G6.allOnes 4) ⊓ G6.coreMod 4 :=
        Subgroup.mem_subgroupOf.mp hmem
      exact B5FinPerm.mem_zpowers_allOnes_iff.mp (Subgroup.mem_inf.mp hk0).1
    · intro hgood
      have hfix : ∀ r ∈ R, ((π' σ : ↥J) : MulAut W) r = r := by
        intro r hr
        let u : ↥R := ⟨r, hr⟩
        obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β' u)
        have hu : ((π' σ : ↥J) : MulAut W) (u : W) ∈ R := hUinv (π' σ) u u.2
        have hm' : G6.permAct 4 σ (m : G6.PermMod 4) ∈ G6.coreMod 4 :=
          hsec σ (m : G6.PermMod 4) m.2
        have hgoodZ : (m : G6.PermMod 4)⁻¹ * G6.permAct 4 σ (m : G6.PermMod 4) ∈
            Subgroup.zpowers (G6.allOnes 4) :=
          B5FinPerm.mem_zpowers_allOnes_iff.mpr
            (hgood (m : G6.PermMod 4) (show (m : G6.PermMod 4) ∈ G6.coreMod 4 from m.2))
        have hmemker : (m : ↥(G6.coreMod 4))⁻¹ *
            (⟨G6.permAct 4 σ (m : G6.PermMod 4), hm'⟩ : ↥(G6.coreMod 4)) ∈
            (Subgroup.zpowers (G6.allOnes 4) ⊓ G6.coreMod 4).subgroupOf (G6.coreMod 4) := by
          rw [Subgroup.mem_subgroupOf]
          exact Subgroup.mem_inf.mpr ⟨hgoodZ,
            Subgroup.mul_mem _ (Subgroup.inv_mem _ m.2) hm'⟩
        have hmk : QuotientGroup.mk m = QuotientGroup.mk
            (⟨G6.permAct 4 σ (m : G6.PermMod 4), hm'⟩ : ↥(G6.coreMod 4)) :=
          QuotientGroup.eq.mpr hmemker
        have h1 : β' (⟨((π' σ : ↥J) : MulAut W) (u : W), hu⟩ : ↥R) = β' u :=
          calc β' (⟨((π' σ : ↥J) : MulAut W) (u : W), hu⟩ : ↥R)
              = QuotientGroup.mk (⟨G6.permAct 4 σ (m : G6.PermMod 4), hm'⟩ :
                  ↥(G6.coreMod 4)) := hβe σ u m hu hm' hm.symm
            _ = QuotientGroup.mk m := hmk.symm
            _ = β' u := hm
        have h2 : ((π' σ : ↥J) : MulAut W) r = r := by
          have := congrArg Subtype.val (hβinj h1)
          simpa [u] using this
        exact h2
      rw [MonoidHom.mem_ker]
      exact Subtype.ext (hfaith (π' σ) (π' σ).2 hfix)
  have hcard_sub : Nat.card {σ : Equiv.Perm (Fin 4) // s15k_jp_sym4_good σ} = 4 := by
    have hExplicit : Nat.card {σ : Equiv.Perm (Fin 4) // ∀ m : G6.PermMod 4,
        (∑ i, Multiplicative.toAdd m i = 0) →
          m⁻¹ * G6.permAct 4 σ m = 1 ∨ m⁻¹ * G6.permAct 4 σ m = G6.allOnes 4} = 4 := by
      rw [Nat.card_eq_fintype_card]
      decide +kernel
    calc Nat.card {σ : Equiv.Perm (Fin 4) // s15k_jp_sym4_good σ}
        = Nat.card {σ : Equiv.Perm (Fin 4) // ∀ m : G6.PermMod 4,
            (∑ i, Multiplicative.toAdd m i = 0) →
              m⁻¹ * G6.permAct 4 σ m = 1 ∨ m⁻¹ * G6.permAct 4 σ m = G6.allOnes 4} :=
          Nat.card_congr (Equiv.subtypeEquivRight (fun σ => ⟨fun h => h, fun h => h⟩))
      _ = 4 := hExplicit
  have hcardker : Nat.card ↥π'.ker = 4 :=
    (Nat.card_congr (Equiv.subtypeEquivRight hP)).trans hcard_sub
  have hperm : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_perm, Nat.card_fin]
    norm_num
  have hcardJ : Nat.card ↥J = 6 := by
    have hcard2 := Subgroup.card_eq_card_quotient_mul_card_subgroup π'.ker
    rw [hperm, hcardker] at hcard2
    have hquot : Nat.card (Equiv.Perm (Fin 4) ⧸ π'.ker) = Nat.card ↥J :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (φ := π') hπ's).toEquiv
    rw [hquot] at hcard2
    omega
  exact ⟨hcardJ, hR4⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
