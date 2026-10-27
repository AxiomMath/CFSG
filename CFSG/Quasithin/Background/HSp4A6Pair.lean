module

public import CFSG.Quasithin.Background.HSp4A6
public import Certificates.Certificate7067

public section

namespace CFSG.Quasithin

namespace H

namespace Sp4A6

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix Equiv PairG
open CFSG.QuasithinUnique.Lin2.Five (tauSp coe_tauSp tauMat)
open scoped Matrix

theorem tau₆_conjB (B : StatedSp 2 (ZMod 2)) (γ : ↥Γ₆) :
    tau₆ (conjB B γ) = conjB (tauSp B) (tau₆ γ) := by
  apply Subtype.ext
  change ((tauSp ⟨_, Γ₆_le (conjB B γ).2⟩ : StatedSp 2 (ZMod 2)) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) =
    ((tauSp B : StatedSp 2 (ZMod 2)) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) *
      ((tauSp ⟨γ, Γ₆_le γ.2⟩ : StatedSp 2 (ZMod 2)) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) *
      ((tauSp B : StatedSp 2 (ZMod 2)) : GL (Fin 2 ⊕ Fin 2) (ZMod 2))⁻¹
  have e : (⟨_, Γ₆_le (conjB B γ).2⟩ : StatedSp 2 (ZMod 2)) = B * ⟨γ, Γ₆_le γ.2⟩ * B⁻¹ :=
    Subtype.ext (coe_conjB B γ)
  rw [e, map_mul, map_mul, map_inv]
  rfl

theorem eq_matAut_of_conj
    {x : MulAut (StdMod (Fin 2 ⊕ Fin 2) (ZMod 2))}
    (M : GL (Fin 2 ⊕ Fin 2) (ZMod 2))
    (h : ∀ γ : ↥Γ₆, x * natAut Γ₆ γ * x⁻¹ = matAut M * natAut Γ₆ γ * (matAut M)⁻¹) :
    x = matAut M := by
  obtain ⟨D, hD⟩ := Sp4.exists_smul_of_conj_eq hasScalarCommutant h
  rcases zmod_two_cases D with h0 | h1
  · exfalso
    have h2 := hD (Pi.single (Sum.inl 0) 1)
    rw [h0, zero_smul, toAddMap_zero, toAddMap_eq_zero_iff] at h2
    have := congrFun h2 (Sum.inl 0)
    simp at this
  · exact toAddMap_injective fun v => by rw [hD, h1, one_smul]

theorem mem_pairSp_of_map
    {x : MulAut (PairMod (Fin 2 ⊕ Fin 2) (ZMod 2))}
    (hx : x ∈ pairNorm Γ₆ tau₆)
    (h1 : (V₁ (Fin 2 ⊕ Fin 2) (ZMod 2)).map x.toMonoidHom = V₁ (Fin 2 ⊕ Fin 2) (ZMod 2)) :
    x ∈ Sp4.pairSp (ZMod 2) := by
  obtain ⟨a, b, rfl⟩ := PairG.exists_pairAut isNatIrr tau₆_surjective not_isoMod hx h1
  have ha := fst_mem_natNorm hx
  obtain ⟨⟨B, ε⟩, hBε⟩ := autΦ_surjective (conjHom Γ₆ ⟨a, ha⟩)
  have hε : ε = false := by
    by_contra hne
    have hε1 : ε = true := by simpa using hne
    subst hε1
    have h2 := natAut_conjHom Γ₆ ⟨a, ha⟩ g₃
    have h3 := Sp4.card_fix_conj a (natAut Γ₆ g₃)
    rw [← h2, ← hBε] at h3
    have h4 : (autΦ (B, true)) g₃ = conjB B (tau₆ g₃) := rfl
    rw [h4, card_fix_conjB, card_fix_tau_g₃, card_fix_g₃] at h3
    omega
  subst hε
  have hconjB : ∀ γ : ↥Γ₆, conjHom Γ₆ ⟨a, ha⟩ γ = conjB B γ := fun γ => by rw [← hBε]; rfl
  have hnatB : ∀ γ : ↥Γ₆, natAut Γ₆ (conjB B γ) =
      matAut (B : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) * natAut Γ₆ γ *
        (matAut (B : GL (Fin 2 ⊕ Fin 2) (ZMod 2)))⁻¹ := by
    intro γ
    change matHom (((conjB B γ : ↥Γ₆) : GL (Fin 2 ⊕ Fin 2) (ZMod 2))) = _
    rw [coe_conjB, map_mul, map_mul, map_inv]
    rfl
  have haB : a = matAut (B : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) := by
    refine eq_matAut_of_conj _ fun γ => ?_
    rw [← hnatB, ← hconjB, natAut_conjHom]
  have hbB : b = matAut ((tauSp B : StatedSp 2 (ZMod 2)) : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) := by
    refine eq_matAut_of_conj _ fun γ => ?_
    obtain ⟨γ₀, rfl⟩ := tau₆_surjective γ
    obtain ⟨δ, hδ1, hδ2⟩ := exists_conj hx γ₀
    have hδ : δ = conjB B γ₀ := by
      apply natAut_injective Γ₆
      rw [← hδ1, hnatB, haB]
    rw [hδ2, hδ, tau₆_conjB]
    change matHom (((conjB (tauSp B) (tau₆ γ₀) : ↥Γ₆) : GL (Fin 2 ⊕ Fin 2) (ZMod 2))) = _
    rw [coe_conjB, map_mul, map_mul, map_inv]
    rfl
  rw [haB, hbB]
  exact ⟨B, rfl⟩

theorem pairNorm_le
    : pairNorm Γ₆ tau₆ ≤ Sp4.pairNormSp (ZMod 2) := by
  intro x hx
  have hs₆ := swapAut_mem_pairNorm tau₆ tau₆_tau₆
  have hs := swapAut_mem_pairNorm (Γ := StatedSp 2 (ZMod 2)) tauSp tauSp_tauSp_two
  rcases PairG.map_V₁_eq_or isNatIrr tau₆_surjective not_isoMod hx with h1 | h1
  · exact pairImg_le_pairNorm _ _ (mem_pairSp_of_map hx h1)
  · have hsx : swapAut (Fin 2 ⊕ Fin 2) (ZMod 2) * x ∈ pairNorm Γ₆ tau₆ :=
      Subgroup.mul_mem _ hs₆ hx
    have hmap : (V₁ (Fin 2 ⊕ Fin 2) (ZMod 2)).map
        (swapAut (Fin 2 ⊕ Fin 2) (ZMod 2) * x).toMonoidHom = V₁ (Fin 2 ⊕ Fin 2) (ZMod 2) := by
      have : (swapAut (Fin 2 ⊕ Fin 2) (ZMod 2) * x).toMonoidHom =
          (swapAut (Fin 2 ⊕ Fin 2) (ZMod 2)).toMonoidHom.comp x.toMonoidHom := rfl
      rw [this, ← Subgroup.map_map, h1]
      have h2 := map_V₁_swapAut (ι := Fin 2 ⊕ Fin 2) (K := ZMod 2)
      rw [← h2, Subgroup.map_map]
      have : (swapAut (Fin 2 ⊕ Fin 2) (ZMod 2)).toMonoidHom.comp
          (swapAut (Fin 2 ⊕ Fin 2) (ZMod 2)).toMonoidHom = MonoidHom.id _ :=
        MonoidHom.ext fun _ => rfl
      rw [this, Subgroup.map_id]
    have h3 := pairImg_le_pairNorm _ _ (mem_pairSp_of_map hsx hmap)
    have : x = (swapAut (Fin 2 ⊕ Fin 2) (ZMod 2))⁻¹ * (swapAut (Fin 2 ⊕ Fin 2) (ZMod 2) * x) := by
      group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hs) h3

@[expose] def vec6 (m : ↥(FFModel.altDn 6).sec) : Fin 6 → ZMod 2 :=
  (Multiplicative.toAdd : Multiplicative (Fin 6 → ZMod 2) ≃ (Fin 6 → ZMod 2)) m.1

@[expose] def mk6 (y : Fin 6 → ZMod 2) (hy : ∑ i, y i = 0) : ↥(FFModel.altDn 6).sec :=
  ⟨(Multiplicative.ofAdd y : G6.PermMod 6), hy⟩

theorem vec6_mul (m m' : ↥(FFModel.altDn 6).sec) : vec6 (m * m') = vec6 m + vec6 m' := rfl

theorem vec6_one : vec6 1 = 0 := rfl

theorem sum_vec6 (m : ↥(FFModel.altDn 6).sec) : ∑ i, vec6 m i = 0 := m.2

@[expose] def coordHom : ↥(FFModel.altDn 6).sec →* StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) where
  toFun m := Multiplicative.ofAdd (coord (vec6 m))
  map_one' := by
    rw [vec6_one, show coord 0 = 0 from funext fun r => by simp [coord]]
    rfl
  map_mul' m m' := by
    rw [vec6_mul, coord_add]
    rfl

theorem coord_smul_ones (k : ℤ) : coord (k • ones) = 0 := by
  funext r
  have := congrFun coord_ones r
  simp only [coord, Pi.zero_apply] at this ⊢
  rw [smul_dotProduct, this, smul_zero]

theorem le_ker_coordHom :
    (FFModel.altDn 6).ker.subgroupOf (FFModel.altDn 6).sec ≤ coordHom.ker := by
  rintro m ⟨⟨k, hk⟩, -⟩
  rw [MonoidHom.mem_ker]
  have hk' : vec6 m = k • ones := by
    have e : (m.1 : G6.PermMod 6) = G6.allOnes 6 ^ k := hk.symm
    unfold vec6
    rw [e, toAdd_zpow]
    rfl
  change Multiplicative.ofAdd (coord (vec6 m)) = 1
  rw [hk', coord_smul_ones]
  rfl

@[expose] noncomputable def coordQ : ↥(FFModel.altDn 6).sec ⧸
    (FFModel.altDn 6).ker.subgroupOf (FFModel.altDn 6).sec →*
      StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  QuotientGroup.lift _ coordHom le_ker_coordHom

theorem coordQ_bijective : Function.Bijective coordQ := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H m =>
      have h0 : coord (vec6 m) = 0 := congrArg Multiplicative.toAdd hq
      obtain ⟨t, ht⟩ := decomp (vec6 m) (sum_vec6 m)
      rw [h0] at ht
      simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, zero_add] at ht
      rw [QuotientGroup.eq_one_iff]
      refine ⟨⟨t.val, ?_⟩, m.2⟩
      change G6.allOnes 6 ^ (t.val : ℤ) = m.1
      apply Multiplicative.toAdd.injective
      change Multiplicative.toAdd (G6.allOnes 6 ^ (t.val : ℤ)) = vec6 m
      rw [toAdd_zpow, ht]
      rcases zmod_two_cases t with rfl | rfl
      · simp
      · change (1 : ℤ) • Multiplicative.toAdd (G6.allOnes 6) = (1 : ZMod 2) • ones
        simp only [one_smul, one_zsmul]
        rfl
  · intro w
    refine ⟨QuotientGroup.mk (mk6 (∑ c, Multiplicative.toAdd w c • bas c) ?_), ?_⟩
    · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_eq_zero fun c _ => by rw [← Finset.mul_sum, sum_bas, mul_zero]
    · change Multiplicative.ofAdd (coord (∑ c, Multiplicative.toAdd w c • bas c)) = w
      rw [coord_sum]
      simp only [coord_smul, coord_bas]
      apply Multiplicative.toAdd.injective
      rw [toAdd_ofAdd]
      funext r
      simp [Finset.sum_apply, Pi.single_apply]

theorem exists_natural
    {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)} {V₁ : Subgroup V}
    {π : ↥(alternatingGroup (Fin 6)) →* ↥H}
    (hπ : (FFModel.altDn 6).RealizesVia H V₁ ⊥ π) :
    ∃ e₁ : ↥V₁ ≃* StdMod (Fin 2 ⊕ Fin 2) (ZMod 2), ∀ (σ : ↥(alternatingGroup (Fin 6)))
      (u : ↥V₁) (hu : ((π σ : ↥H) : MulAut V) (u : V) ∈ V₁),
      e₁ ⟨_, hu⟩ = matAut (psiHom σ) (e₁ u) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hπ
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  let e₁ : ↥V₁ ≃* StdMod (Fin 2 ⊕ Fin 2) (ZMod 2) :=
    (MulEquiv.ofBijective β ⟨hβi, hβs⟩).trans (MulEquiv.ofBijective coordQ coordQ_bijective)
  refine ⟨e₁, fun σ u hu => ?_⟩
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
  have hm' : (FFModel.altDn 6).act σ m.1 ∈ (FFModel.altDn 6).sec :=
    G6.permAct_mem_coreMod (σ : Perm (Fin 6)) m.2
  have h1 := hβe σ u m hu hm' hm.symm
  calc e₁ ⟨_, hu⟩ = coordQ (β ⟨_, hu⟩) := rfl
    _ = coordQ (QuotientGroup.mk ⟨(FFModel.altDn 6).act σ m.1, hm'⟩) := congrArg coordQ h1
    _ = Multiplicative.ofAdd (coord (perm6 σ (vec6 m))) := rfl
    _ = Multiplicative.ofAdd (psiMat σ *ᵥ coord (vec6 m)) := by
        rw [coord_perm6 _ (sum_vec6 m)]
    _ = matAut (psiHom σ) (coordQ (QuotientGroup.mk m)) := rfl
    _ = matAut (psiHom σ) (coordQ (β u)) :=
        congrArg (fun z => matAut (psiHom σ) (coordQ z)) hm
    _ = matAut (psiHom σ) (e₁ u) := rfl

theorem H7_A6Pair
    {V : Type*} [CommGroup V] [Finite V] {H M : Subgroup (MulAut V)}
    {V₁ : Subgroup V} (hreal : AlternatingNatural H V₁ ⊥ 6) {φ : MulAut V}
    (hφ : φ ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hinf : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥) (hsup : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤)
    (hniso : ¬ Pair.IsoMod H V₁ (V₁.map φ.toMonoidHom))
    (hMN : M ≤ Subgroup.normalizer (H : Set (MulAut V))) :
    E3.aParam M < 2 ∧ 3 ≤ E3.mParam M := by
  obtain ⟨π, hπ⟩ := hreal
  have hπs : Function.Surjective π := hπ.1
  have hU : ∀ h : ↥H, ∀ u ∈ V₁, (h : MulAut V) u ∈ V₁ := hπ.2.2.2.1
  obtain ⟨e₁, he₁⟩ := exists_natural hπ
  set π' : ↥Γ₆ →* ↥H := π.comp psiEquiv.symm.toMonoidHom with hπ'
  have hπ's : Function.Surjective π' := hπs.comp psiEquiv.symm.surjective
  have he₁' : ∀ (γ : ↥Γ₆) (u : ↥V₁) (hu : ((π' γ : ↥H) : MulAut V) (u : V) ∈ V₁),
      e₁ ⟨_, hu⟩ = matAut (γ : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) (e₁ u) := by
    intro γ u hu
    have h := he₁ (psiEquiv.symm γ) u hu
    have e : psiHom ((psiEquiv.symm γ : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) =
        (γ : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) := by
      have := congrArg Subtype.val (psiEquiv.apply_symm_apply γ)
      exact this
    rw [← e]
    exact h
  obtain ⟨e, he⟩ := PairG.exists_pair_model tau₆ π' hπ's hU e₁ he₁' hAut hφ hinf hsup hniso
  have : Finite (PairMod (Fin 2 ⊕ Fin 2) (ZMod 2)) := Finite.of_equiv V e.toEquiv
  have h2 : M.map (congrHom e) ≤ Sp4.pairNormSp (ZMod 2) :=
    (PairG.map_le_pairNorm tau₆ e he hMN).trans pairNorm_le
  have hK : Nat.card (ZMod 2) = 2 ^ 1 := by rw [Nat.card_zmod, pow_one]
  refine ⟨?_, ?_⟩
  · rw [← aParam_map_congrHom e]
    exact Sp4.aParam_lt le_rfl hK h2
  · rw [← mParam_map_congrHom e]
    exact Sp4.le_mParam le_rfl hK h2

end Sp4A6

end H

end CFSG.Quasithin
