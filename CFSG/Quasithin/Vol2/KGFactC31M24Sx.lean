module

public import CFSG.Quasithin.Vol2.KGFactC31M24Sext
public import CFSG.Quasithin.Vol2.KGFactC31M24Q

public section

namespace CFSG.Quasithin.KGC31.M24

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.KGC31
  _root_.Certificates

variable {A : Type} [Group A] [Finite A]

theorem isElemAbelian_eSub {Γ : Type*} [Group Γ] {k : ℕ} {v : Fin k → Γ} (hv : EBasis v) :
    IsElemAbelian 2 (eSub hv) :=
  ⟨⟨⟨fun a b => Subtype.ext (eSub_comm hv a b a.2 b.2)⟩⟩, fun x hx => by
    rw [sq]
    exact eSub_sq hv x hx⟩

theorem not_isPGroup_alt6 : ¬ IsPGroup 2 ↥(alternatingGroup (Fin 6)) := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h
  rw [card_alt6] at hk
  have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 360)
  have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
  omega

theorem concl_sextet
    {S M₀ R M V : Subgroup A}
    (h : Setup S M₀ R M V) {f : G₀ →* A} (hf : Iso f) (hR : R = (eSub basis_s).map f) {y : A}
    (hy : y ∈ M₀) (hyk : ∃ k, y ^ 5 ^ k = 1) (hy1 : y ≠ 1) : Concl S M₀ R M V := by
  have hN : Subgroup.normalizer (R : Set A) = (eNorm basis_s).map f := by
    rw [hR, hf.map_normalizer]
  have hNsN : Ns.map f ≤ Subgroup.normalizer (R : Set A) := by
    rw [hN]
    exact Subgroup.map_mono Ns_le
  have hRc : Nat.card R = 64 := by rw [hR, hf.card_map, card_eSub]; norm_num
  have hdvd : 138240 ∣ Nat.card (Subgroup.normalizer (R : Set A)) := by
    rw [← card_Ns, ← hf.card_map]
    exact card_dvd_of_le hNsN
  have hNc : Nat.card (Subgroup.normalizer (R : Set A)) = 138240 := by
    rcases card_normalizer_eq hf h.R_ne_bot (by rw [hRc]; norm_num) h.hrad hNsN
        (by rw [card_Ns]; norm_num) with
      ⟨-, h2⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩ | ⟨-, h2⟩
    · rw [hRc] at h2; norm_num at h2
    · rw [h1] at hdvd; norm_num at hdvd
    · exact h1
    all_goals rw [hRc] at h2; norm_num at h2
  have hLsN : Ls.map f ≤ Subgroup.normalizer (R : Set A) := by
    rw [hN]
    exact Subgroup.map_mono Ls_le
  have hi : (Ls.map f).relIndex (Subgroup.normalizer (R : Set A)) ≤ 4 := by
    have h1 := (Ls.map f).relIndex_mul_card (K := Subgroup.normalizer (R : Set A))
    rw [inf_eq_left.mpr hLsN, hNc, hf.card_map, card_Ls] at h1
    omega
  have hM₀Ls : M₀ ≤ Ls.map f := le_of_perfect_of_relIndex_le h.hM₀R h.hper hi
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hy5N : f y5 ∈ Subgroup.normalizer (R : Set A) := by
    rw [hN]
    exact ⟨y5, y5_mem, rfl⟩
  have hoy5 : orderOf (f y5) = 5 := by rw [orderOf_injective f hf.inj, orderOf_y5]
  have hNp : ¬ 5 ^ 2 ∣ Nat.card (Subgroup.normalizer (R : Set A)) := by rw [hNc]; norm_num
  have hy5M : f y5 ∈ M₀ :=
    mem_of_sylow hy5N hoy5 hNp h.hM₀R h.normal_in_normalizer hy hyk hy1
  have hLsM : Ls.map f ≤ M₀ := by
    rw [Subgroup.map_le_iff_le_comap]
    refine conjGenOf_le fun w hw => ?_
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    have hmN : f (elt w) ∈ Subgroup.normalizer (R : Set A) := by
      rw [hN]
      exact ⟨elt w, nj_mem w hw, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (h.normal_in_normalizer hmN) (f y5)).mp hy5M
  have hM₀eq : M₀ = Ls.map f := le_antisymm hM₀Ls hLsM
  have hRM₀ : R ≤ M₀ := by
    rw [hR, hM₀eq]
    exact Subgroup.map_mono s_le_Ls
  have hcM₀ : Nat.card M₀ = 69120 := by rw [hM₀eq, hf.card_map, card_Ls]
  have hLsperf : ⁅Ls, Ls⁆ = Ls := by
    apply Subgroup.map_injective hf.inj
    rw [Subgroup.map_commutator, ← hM₀eq, h.hper]
  obtain ⟨ψ₀, hψs, hψk, hψR⟩ := ls_alt_data hLsperf
  let e : ↥Ls ≃* ↥M₀ :=
    (Ls.equivMapOfInjective f hf.inj).trans (MulEquiv.subgroupCongr hM₀eq.symm)
  have he : ∀ x : ↥Ls, ((e x : ↥M₀) : A) = f x := fun _ => rfl
  let ψ : ↥M₀ →* ↥(alternatingGroup (Fin 6)) := ψ₀.comp e.symm.toMonoidHom
  have hψsurj : Function.Surjective ψ := hψs.comp e.symm.surjective
  have hψker : ψ.ker = ψ₀.ker.map e.toMonoidHom := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_map]
    constructor
    · intro hx
      exact ⟨e.symm x, hx, by simp⟩
    · rintro ⟨z, hz, rfl⟩
      show ψ₀ (e.symm (e z)) = 1
      rw [MulEquiv.symm_apply_apply]
      exact hz
  have hψk' : Nat.card ψ.ker = 192 := by
    rw [hψker, Subgroup.card_map_of_injective e.injective, hψk]
  have hRle : R.subgroupOf M₀ ≤ ψ.ker := by
    intro x hx
    rw [Subgroup.mem_subgroupOf, hR] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    have h1 : ((e.symm x : ↥Ls) : G₀) = z := by
      apply hf.inj
      rw [hzx, ← he, MulEquiv.apply_symm_apply]
    rw [MonoidHom.mem_ker]
    show ψ₀ (e.symm x) = 1
    exact hψR (Subgroup.mem_subgroupOf.mpr (h1 ▸ hz))
  have hRn : (R.subgroupOf M₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRM₀).mpr h.hM₀R
  let φ : ↥M₀ ⧸ R.subgroupOf M₀ →* ↥(alternatingGroup (Fin 6)) := QuotientGroup.lift _ ψ hRle
  have hφs : Function.Surjective φ := by
    intro σ
    obtain ⟨x, hx⟩ := hψsurj σ
    exact ⟨QuotientGroup.mk x, by rw [QuotientGroup.lift_mk]; exact hx⟩
  have hRMc : Nat.card (R.subgroupOf M₀) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM₀).toEquiv, hRc]
  have hcq : Nat.card (↥M₀ ⧸ R.subgroupOf M₀) = 1080 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (R.subgroupOf M₀)
    rw [hcM₀, hRMc] at this
    omega
  have hφk : Nat.card φ.ker = 3 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv, card_alt6,
      hcq] at h1
    omega
  have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hperfQ : commutator (↥M₀ ⧸ R.subgroupOf M₀) = ⊤ := by
    have hcommM : commutator ↥M₀ = ⊤ := by
      apply Subgroup.map_injective M₀.subtype_injective
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype, h.hper]
    rw [commutator_def, ← Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective (R.subgroupOf M₀)), ← Subgroup.map_commutator,
      ← commutator_def, hcommM]
  have hhat : CFSG.Quasithin.IsHat (↥M₀ ⧸ R.subgroupOf M₀) ↥(alternatingGroup (Fin 6)) :=
    isHat_of_surj (H13.alternatingGroup_nonabelian (by norm_num)) hperfQ φ hφs hφk
  have hO : pCoreOf 2 M₀ = R := pCoreOf_eq_of_surj hRM₀ h.hR2
    (QuotientGroup.mk' (R.subgroupOf M₀)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) (noNormalTwo_of_isHat hhat (noNormalTwo_of_simple not_isPGroup_alt6))
  have hCR : Subgroup.centralizer (R : Set A) = R := by
    rw [hR, ← hf.map_centralizer, cent_s]
  have hC : M₀ ⊓ Subgroup.centralizer (R : Set A) ≤ R := by
    rw [hCR]
    exact inf_le_right
  have hvA : EBasis fun i => f (vS i) := basis_s.map hf.inj
  have hRA : R = eSub hvA := by rw [hR, eSub_map basis_s hf.inj]
  have hEA : IsElemAbelian 2 R := hRA ▸ isElemAbelian_eSub hvA
  have hblock := isHatA6Block_of hEA hRM₀ h.hM₀R hO hRc hC h.hper hhat
  have hVR : V = R :=
    (irr_of_hat hEA h.hM₀R hRc hC hhat h.hVR h.hM₀V).resolve_left h.hVne
  have hM₀ : conjClosure M₀ M = M₀ := conjClosure_eq_self' h.hMN
  refine ⟨Or.inr (Or.inr (Or.inl ⟨h.hSs, Or.inl ?_⟩)),
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl h.hSs, hblock⟩)))),
    summand_of_card64 (by rw [hVR, hRc])⟩
  rw [hM₀]
  exact ⟨R.subgroupOf M₀, hRn, ⟨(Subgroup.subgroupOfEquivOfLe hRM₀).trans
    ((MulEquiv.subgroupCongr hRA).trans (ecoords hvA))⟩, hhat⟩

end CFSG.Quasithin.KGC31.M24

end
