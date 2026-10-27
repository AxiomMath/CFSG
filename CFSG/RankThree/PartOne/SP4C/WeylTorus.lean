module

public import CFSG.RankThree.PartOne.SP4C.TauTorus

public section

namespace CFSG.RankThree.PartOne.SP4C

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.LieType.Universal.Unitary Matrix
open CFSG.Assembly.LowTwoRank

variable {p : ℕ} {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def Tsub (p : ℕ) (K : Type) [Field K] [CharP K 2] : Subgroup ↥(spRev K) :=
  (d8Tor p K 4).subgroupOf (spRev K)

theorem torC_mem (v : D8Mod p K) : torC p K v ∈ Tsub p K := by
  show ((torC p K v : ↥(spRev K)) : GL (Fin 4) K) ∈ d8Tor p K 4
  exact ⟨v, (coe_torC v).symm⟩

@[expose] noncomputable def torT (p : ℕ) (K : Type) [Field K] [CharP K 2] :
    D8Mod p K ≃* ↥(Tsub p K) :=
  MulEquiv.ofBijective ((torC p K).codRestrict (Tsub p K) torC_mem) ⟨fun v w h =>
    torC_injective (congrArg (fun t : ↥(Tsub p K) => (t : ↥(spRev K))) h), fun t => by
      obtain ⟨v, hv⟩ := t.2
      refine ⟨v, Subtype.ext (Subtype.ext ?_)⟩
      show ((torC p K v : ↥(spRev K)) : GL (Fin 4) K) = ((t : ↥(spRev K)) : GL (Fin 4) K)
      rw [coe_torC]
      exact hv⟩

theorem coe_torT (v : D8Mod p K) : ((torT p K v : ↥(Tsub p K)) : ↥(spRev K)) = torC p K v := rfl

theorem hT_spRev (v : D8Mod p K) : (diagU (d8Vec 4 v) : GL (Fin 4) K) ∈ spRev K := by
  rw [d8Vec_four]
  exact diagU_dvec4_mem_spRev _ _

theorem hP_spRev (τ : Equiv.Perm (Fin 4)) (hτ : ∀ i, τ (Fin.rev i) = Fin.rev (τ i)) :
    (permGL τ : GL (Fin 4) K) ∈ spRev K := by
  rw [mem_spRev_iff]
  simpa [conjTr] using permGL_gram (RingEquiv.refl K) τ hτ

theorem exists_perm_elt (γ : DihedralGroup 4) :
    ∃ m : ↥(spRev K), m ∈ Subgroup.normalizer (Tsub p K : Set ↥(spRev K)) ∧
      ∀ v : D8Mod p K, m * torC p K v * m⁻¹ = torC p K (d8Act γ v) := by
  classical
  have hTM : d8Tor p K 4 ≤ spRev K := by
    rintro _ ⟨v, rfl⟩
    exact hT_spRev v
  have hdmem : ∀ v : D8Mod p K, (diagU (d8Vec 4 v) : GL (Fin 4) K) ∈ d8Tor p K 4 :=
    fun v => ⟨v, rfl⟩
  have hconj : ∀ (γ : DihedralGroup 4) (v : D8Mod p K),
      (permGL (d8Perm d8Comb_four γ) : GL (Fin 4) K) * diagU (d8Vec 4 v) *
        (permGL (d8Perm d8Comb_four γ) : GL (Fin 4) K)⁻¹ = diagU (d8Vec 4 (d8Act γ v)) := by
    intro γ v
    rw [permGL_conj_diagU, d8Vec_act d8Comb_four]
  set g₀ : ↥(spRev K) := ⟨permGL (d8Perm d8Comb_four γ),
    hP_spRev _ (d8Comb2_four.comm_rev γ)⟩ with hg₀
  have hg : g₀ ∈ Subgroup.normalizer (Tsub p K : Set ↥(spRev K)) := by
    rw [Tsub, mem_normalizer_subgroupOf_iff hTM]
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · obtain ⟨v, rfl⟩ := hx
      show (permGL (d8Perm d8Comb_four γ) : GL (Fin 4) K) * diagU (d8Vec 4 v) *
        (permGL (d8Perm d8Comb_four γ) : GL (Fin 4) K)⁻¹ ∈ d8Tor p K 4
      rw [hconj]
      exact hdmem _
    · obtain ⟨v, rfl⟩ := hx
      show (permGL (d8Perm d8Comb_four γ) : GL (Fin 4) K)⁻¹ * diagU (d8Vec 4 v) *
        (permGL (d8Perm d8Comb_four γ) : GL (Fin 4) K) ∈ d8Tor p K 4
      have h1 : (permGL (d8Perm d8Comb_four γ) : GL (Fin 4) K)⁻¹ =
          permGL (d8Perm d8Comb_four γ⁻¹) := by rw [map_inv, map_inv]
      have h2 : (permGL (d8Perm d8Comb_four γ) : GL (Fin 4) K) =
          (permGL (d8Perm d8Comb_four γ⁻¹) : GL (Fin 4) K)⁻¹ := by
        rw [map_inv, map_inv, inv_inv]
      rw [h1, h2, hconj]
      exact hdmem _
  refine ⟨g₀, hg, fun v => ?_⟩
  apply Subtype.ext
  show (permGL (d8Perm d8Comb_four γ) : GL (Fin 4) K) * ((torC p K v : ↥(spRev K)) :
    GL (Fin 4) K) * (permGL (d8Perm d8Comb_four γ) : GL (Fin 4) K)⁻¹ = _
  rw [coe_torC, hconj, coe_torC]

theorem exists_weyl [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    {m : ↥(spRev K)} (hm : m ∈ Subgroup.normalizer (Tsub p K : Set ↥(spRev K))) :
    ∃ γ : DihedralGroup 4, ∀ v : D8Mod p K, m * torC p K v * m⁻¹ = torC p K (d8Act γ v) := by
  classical
  obtain ⟨SM⟩ := exists_d8ctx d8Comb_four d8Comb2_four hp hp2 hζ (spRev K) hT_spRev hP_spRev
  have hinj : Function.Injective (d8Act : DihedralGroup 4 →* MulAut (D8Mod p K)) :=
    d8Act_injective hp hp2 hζ
  let Ψ : DihedralGroup 4 →* MulAut ↥(Tsub p K) :=
    (MulAut.congr (torT p K)).toMonoidHom.comp d8Act
  let Ψ' : DihedralGroup 4 →* MulAut ↥(Tsub p K) :=
    (MulAut.congr SM.tor).toMonoidHom.comp d8Act
  let Φ : ↥(Subgroup.normalizer (Tsub p K : Set ↥(spRev K))) →* MulAut ↥(Tsub p K) :=
    (Tsub p K).normalizerMonoidHom
  have hA : ∀ γ : DihedralGroup 4, ∃ g : ↥(Subgroup.normalizer (Tsub p K : Set ↥(spRev K))),
      Φ g = Ψ γ := by
    intro γ
    obtain ⟨g₀, hg, hg₀⟩ := exists_perm_elt (p := p) (K := K) γ
    refine ⟨⟨g₀, hg⟩, MulEquiv.ext fun t => ?_⟩
    obtain ⟨v, rfl⟩ := (torT p K).surjective t
    have hΨ : Ψ γ (torT p K v) = torT p K (d8Act γ v) := by
      simp [Ψ, MulAut.congr_apply]
    rw [hΨ]
    apply Subtype.ext
    exact hg₀ v
  have hrange_le : Φ.range ≤ Ψ'.range := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨γ', hγ'⟩ := SM.induced (g : ↥(spRev K)) g.2 (Subgroup.mem_top _)
    exact ⟨γ', hγ'.symm⟩
  have hΨinj : Function.Injective Ψ := by
    intro a b h
    apply hinj
    exact (MulAut.congr (torT p K)).injective h
  have hcardΨ : Nat.card Ψ.range = 8 := by
    have h1 := Subgroup.card_ker_mul_card_range Ψ
    rw [(MonoidHom.ker_eq_bot_iff Ψ).2 hΨinj, Subgroup.card_bot, one_mul,
      DihedralGroup.nat_card] at h1
    omega
  have hcardΨ' : Nat.card Ψ'.range ≤ 8 := by
    have h1 := Subgroup.card_range_dvd Ψ'
    rw [DihedralGroup.nat_card] at h1
    exact Nat.le_of_dvd (by norm_num) h1
  have hΨΦ : Ψ.range ≤ Φ.range := by
    rintro _ ⟨γ, rfl⟩
    obtain ⟨g, hg⟩ := hA γ
    exact ⟨g, hg⟩
  have hcardΦ : Nat.card Φ.range ≤ Nat.card Ψ.range := by
    rw [hcardΨ]
    exact (Subgroup.card_le_of_le hrange_le).trans hcardΨ'
  have heq : Ψ.range = Φ.range := Subgroup.eq_of_le_of_card_ge hΨΦ hcardΦ
  have hmem : Φ ⟨m, hm⟩ ∈ Ψ.range := by
    rw [heq]
    exact ⟨⟨m, hm⟩, rfl⟩
  obtain ⟨γ, hγ⟩ := hmem
  refine ⟨γ, fun v => ?_⟩
  have h1 := congrArg (fun φ : MulAut ↥(Tsub p K) => ((φ (torT p K v) : ↥(Tsub p K)) :
    ↥(spRev K))) hγ
  simp only [Ψ] at h1
  simpa [Φ, MulAut.congr_apply, coe_torT] using h1.symm

end CFSG.RankThree.PartOne.SP4C
