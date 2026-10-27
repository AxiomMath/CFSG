module

public import CFSG.Quasithin.Recognition.RuTypeJ11b
public import CFSG.Quasithin.Recognition.RuRank3T1
public import CFSG.Quasithin.Recognition.RuRank3E0L225
public import CFSG.Quasithin.Recognition.RuRank3Iface

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits
open MulAction

namespace RuDataM

variable {G : Type} [Group G] [Finite G] (M : RuDataM G)

theorem exists_conj_sylow_five
    (φ : ↥(M.F1 ⊔ M.F2) ≃* titsA) :
    ∃ P : Subgroup G, P ≤ M.F1 ⊔ M.F2 ∧ Nat.card P = 25 ∧
      ∃ g : G, g ∉ M.F1 ⊔ M.F2 ∧ ∀ x ∈ P, g⁻¹ * x * g ∈ P := by
  have hp5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hFcard := card_F_of φ
  obtain ⟨PF, hPF⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(M.F1 ⊔ M.F2)) 5 (n := 2)
    (by rw [hFcard]; norm_num)
  have hPcard : Nat.card (PF.map (M.F1 ⊔ M.F2).subtype) = 25 := by
    rw [Subgroup.card_map_of_injective (M.F1 ⊔ M.F2).subtype_injective, hPF]
    norm_num
  have hPle : PF.map (M.F1 ⊔ M.F2).subtype ≤ M.F1 ⊔ M.F2 := Subgroup.map_subtype_le _
  have hPp : IsPGroup 5 (PF.map (M.F1 ⊔ M.F2).subtype) :=
    IsPGroup.of_card (n := 2) (by rw [hPcard]; norm_num)
  obtain ⟨R, hPR⟩ := hPp.exists_le_sylow
  have hRcard : Nat.card (R : Subgroup G) = 125 := by
    have hbH := M.b5el_mem_H
    have hb5 := M.orderOf_b5el
    have hcardG := M.card_eq
    have hP5syl : IsPGroup 5 (P5 M.b5el) :=
      IsPGroup.of_card (n := 3) (by rw [card_P5_eq_125 hbH hb5]; norm_num)
    have hP5idx : ¬ 5 ∣ (P5 M.b5el).index := by
      intro hd
      have h := Subgroup.card_mul_index (P5 M.b5el)
      rw [card_P5_eq_125 hbH hb5, hcardG] at h
      obtain ⟨c, hc⟩ := hd
      rw [hc] at h
      norm_num at h
      omega
    rw [Sylow.card_eq_multiplicity R, ← Sylow.card_eq_multiplicity (hP5syl.toSylow hP5idx),
      IsPGroup.toSylow_coe, card_P5_eq_125 hbH hb5]
  have hidx : ((PF.map (M.F1 ⊔ M.F2).subtype).subgroupOf (R : Subgroup G)).index = 5 := by
    have h := Subgroup.card_mul_index ((PF.map (M.F1 ⊔ M.F2).subtype).subgroupOf (R : Subgroup G))
    rw [card_subgroupOf_of_le hPR, hPcard, hRcard] at h
    omega
  have hN : ((PF.map (M.F1 ⊔ M.F2).subtype).subgroupOf (R : Subgroup G)).Normal :=
    Subgroup.normal_of_index_eq_minFac_card (by rw [hidx, hRcard]; norm_num)
  have hRF : (R : Subgroup G) ⊓ (M.F1 ⊔ M.F2) = PF.map (M.F1 ⊔ M.F2).subtype := by
    symm
    apply Subgroup.eq_of_le_of_card_ge (le_inf hPR hPle)
    have h1 : Nat.card ↥((R : Subgroup G) ⊓ (M.F1 ⊔ M.F2)) ∣ 125 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : (R : Subgroup G) ⊓ (M.F1 ⊔ M.F2) ≤ R)
      rwa [hRcard] at this
    have h2 : Nat.card ↥((R : Subgroup G) ⊓ (M.F1 ⊔ M.F2)) ∣ 35942400 := by
      have := Subgroup.card_dvd_of_le
        (inf_le_right : (R : Subgroup G) ⊓ (M.F1 ⊔ M.F2) ≤ M.F1 ⊔ M.F2)
      rwa [hFcard] at this
    have h3 : Nat.card ↥((R : Subgroup G) ⊓ (M.F1 ⊔ M.F2)) ∣ 25 := by
      have := Nat.dvd_gcd h1 h2
      norm_num at this
      exact this
    rw [hPcard]
    exact Nat.le_of_dvd (by norm_num) h3
  obtain ⟨g, hgR, hgP⟩ : ∃ g ∈ (R : Subgroup G), g ∉ PF.map (M.F1 ⊔ M.F2).subtype := by
    by_contra hcon
    have hle : (R : Subgroup G) ≤ PF.map (M.F1 ⊔ M.F2).subtype := fun x hx => by
      by_contra hx'
      exact hcon ⟨x, hx, hx'⟩
    have := Subgroup.card_le_of_le hle
    rw [hRcard, hPcard] at this
    norm_num at this
  refine ⟨PF.map (M.F1 ⊔ M.F2).subtype, hPle, hPcard, g, fun hgF => hgP ?_, fun x hx => ?_⟩
  · rw [← hRF]
    exact Subgroup.mem_inf.mpr ⟨hgR, hgF⟩
  · have h := hN.conj_mem ⟨x, hPR hx⟩ (by rw [Subgroup.mem_subgroupOf]; exact hx)
      ⟨g⁻¹, inv_mem hgR⟩
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h

theorem isRudvalisRank3
    (φ : ↥(M.F1 ⊔ M.F2) ≃* titsA) : RuRank3.IsRudvalisRank3 G (G ⧸ (M.F1 ⊔ M.F2)) := by
  have hC := M.centralizer_Fd_F_eq_bot φ
  have hΩ := M.card_quotient_F φ
  obtain ⟨ω₀, hω₀⟩ : ∃ ω₀ : G ⧸ (M.F1 ⊔ M.F2), ω₀ = ((1 : G) : G ⧸ (M.F1 ⊔ M.F2)) := ⟨_, rfl⟩
  have hstab : stabilizer G ω₀ = M.F1 ⊔ M.F2 := by
    rw [hω₀]
    exact stabilizer_quotient _
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ↥(stabilizer G ω₀) ≃* titsA, ∀ x (hx : x ∈ stabilizer G ω₀)
      (hxF : x ∈ M.F1 ⊔ M.F2), ψ ⟨x, hx⟩ = φ ⟨x, hxF⟩ :=
    ⟨(MulEquiv.subgroupCongr hstab).trans φ, fun _ _ _ => rfl⟩
  have horb : ∀ z : G ⧸ (M.F1 ⊔ M.F2), (orbit (stabilizer G ω₀) z).ncard *
      Nat.card (stabilizer (stabilizer G ω₀) z) = 35942400 := by
    intro z
    rw [← index_stabilizer, mul_comm, Subgroup.card_mul_index, hstab, card_F_of φ]
  have hωorb : orbit (stabilizer G ω₀) ω₀ = {ω₀} := by
    ext z
    constructor
    · rintro ⟨f, rfl⟩
      exact f.2
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact mem_orbit_self ω₀
  have hn0 : (orbit (stabilizer G ω₀) ω₀).ncard = 1 := by rw [hωorb, Set.ncard_singleton]
  have hdisj : ∀ a b : G ⧸ (M.F1 ⊔ M.F2), a ∉ orbit (stabilizer G ω₀) b →
      Disjoint (orbit (stabilizer G ω₀) a) (orbit (stabilizer G ω₀) b) := by
    intro a b hab
    rw [Set.disjoint_left]
    intro z hza hzb
    apply hab
    rw [← orbit_eq_iff, ← orbit_eq_iff.2 hza]
    exact orbit_eq_iff.2 hzb
  obtain ⟨h, hhQ, hhF1⟩ := M.exists_mem_Q_not_mem_F1
  obtain ⟨δ, hδ⟩ : ∃ δ : G ⧸ (M.F1 ⊔ M.F2), δ = (h : G ⧸ (M.F1 ⊔ M.F2)) := ⟨_, rfl⟩
  have hδcard : Nat.card (stabilizer (stabilizer G ω₀) δ) = 2 ^ 12 * 5 := by
    rw [J11.card_stabilizer_subgroup, hstab, hδ, J11.stabilizer_mk,
      M.inf_conj_eq_F1 φ hC hhQ hhF1, M.card_F1]
  have hn1 : (orbit (stabilizer G ω₀) δ).ncard = 1755 := by
    have := horb δ
    rw [hδcard] at this
    omega
  have hδω : δ ∉ orbit (stabilizer G ω₀) ω₀ := by
    intro hmem
    have := hn1
    rw [orbit_eq_iff.2 hmem, hn0] at this
    norm_num at this
  obtain ⟨P, hPF, hPcard, g, hgF, hgP⟩ := M.exists_conj_sylow_five φ
  obtain ⟨γ, hγ⟩ : ∃ γ : G ⧸ (M.F1 ⊔ M.F2), γ = (g : G ⧸ (M.F1 ⊔ M.F2)) := ⟨_, rfl⟩
  have hγstab : stabilizer G γ = (M.F1 ⊔ M.F2).map (MulAut.conj g).toMonoidHom := by
    rw [hγ]
    exact J11.stabilizer_mk _ g
  have hPγ : P ≤ (M.F1 ⊔ M.F2) ⊓ stabilizer G γ := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨hPF hx, ?_⟩
    rw [hγstab, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    exact hPF (hgP x hx)
  have h25 : 25 ∣ Nat.card (stabilizer (stabilizer G ω₀) γ) := by
    rw [J11.card_stabilizer_subgroup, hstab, ← hPcard]
    exact Subgroup.card_dvd_of_le hPγ
  have hγF : ¬ (M.F1 ⊔ M.F2 ≤ stabilizer G γ) := by
    intro hle
    apply hgF
    have hN : g⁻¹ ∈ Subgroup.normalizer ((M.F1 ⊔ M.F2 : Subgroup G) : Set G) :=
      mem_normalizer_of_conj_mem fun x hx => by
        have := hle hx
        rw [hγstab, Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at this
        rwa [inv_inv]
    have := inv_mem (normalizer_F_le φ hC hN)
    rwa [inv_inv] at this
  have hγD : ¬ (Fd φ ≤ stabilizer G γ) := by
    intro hle
    apply hgF
    have hle' : (Fd φ).map (MulAut.conj g⁻¹).toMonoidHom ≤ M.F1 ⊔ M.F2 := by
      rintro _ ⟨x, hx, rfl⟩
      have := hle hx
      rw [hγstab, Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at this
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact this
    have hcard : Nat.card ((Fd φ).map (MulAut.conj g⁻¹).toMonoidHom) = 17971200 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, card_Fd]
    have heq := eq_Fd_of_le φ hle' hcard
    have hN : g⁻¹ ∈ Subgroup.normalizer (Fd φ : Set G) :=
      mem_normalizer_of_conj_mem fun x hx => by
        have : g⁻¹ * x * g⁻¹⁻¹ ∈ (Fd φ).map (MulAut.conj g⁻¹).toMonoidHom :=
          ⟨x, hx, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
        rwa [heq] at this
    have := inv_mem (normalizer_Fd_le φ hC hN)
    rwa [inv_inv] at this
  have hγω : γ ∉ orbit (stabilizer G ω₀) ω₀ := by
    rw [hωorb, Set.mem_singleton_iff]
    intro hγω
    apply hγF
    rw [hγω, hstab]
  have hγδ : γ ∉ orbit (stabilizer G ω₀) δ := by
    intro hmem
    have h1 := horb γ
    rw [orbit_eq_iff.2 hmem, hn1] at h1
    omega
  have hle2304 : (orbit (stabilizer G ω₀) γ).ncard ≤ 2304 := by
    have d1 : Disjoint (orbit (stabilizer G ω₀) ω₀) (orbit (stabilizer G ω₀) δ) :=
      (hdisj δ ω₀ hδω).symm
    have d2 : Disjoint (orbit (stabilizer G ω₀) ω₀ ∪ orbit (stabilizer G ω₀) δ)
        (orbit (stabilizer G ω₀) γ) :=
      Set.disjoint_union_left.mpr ⟨(hdisj γ ω₀ hγω).symm, (hdisj γ δ hγδ).symm⟩
    have hu := Set.ncard_le_ncard (Set.subset_univ (orbit (stabilizer G ω₀) ω₀ ∪
      orbit (stabilizer G ω₀) δ ∪ orbit (stabilizer G ω₀) γ)) (Set.toFinite _)
    rw [Set.ncard_univ, hΩ, Set.ncard_union_eq d2 (Set.toFinite _) (Set.toFinite _),
      Set.ncard_union_eq d1 (Set.toFinite _) (Set.toFinite _), hn0, hn1] at hu
    omega
  have hmemK : ∀ x (hx : x ∈ stabilizer G ω₀),
      ψ ⟨x, hx⟩ ∈ (stabilizer (stabilizer G ω₀) γ).map ψ.toMonoidHom → x ∈ stabilizer G γ := by
    intro x hx hK
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at hK
    exact hK
  have hK25 : 25 ∣ Nat.card ((stabilizer (stabilizer G ω₀) γ).map ψ.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective ψ.injective]
    exact h25
  have hKidx : ((stabilizer (stabilizer G ω₀) γ).map ψ.toMonoidHom).index ≤ 2304 := by
    rw [Subgroup.index_map_of_bijective (f := ψ.toMonoidHom) ψ.bijective, index_stabilizer]
    exact hle2304
  have hKtop : (stabilizer (stabilizer G ω₀) γ).map ψ.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hγF
    intro x hx
    have hx' : x ∈ stabilizer G ω₀ := by rw [hstab]; exact hx
    apply hmemK x hx'
    rw [htop]
    exact Subgroup.mem_top _
  have hKD : (stabilizer (stabilizer G ω₀) γ).map ψ.toMonoidHom ≠ titsD.subgroupOf titsA := by
    intro hD
    apply hγD
    intro x hx
    have hxF : x ∈ M.F1 ⊔ M.F2 := Fd_le φ hx
    have hx' : x ∈ stabilizer G ω₀ := by rw [hstab]; exact hxF
    apply hmemK x hx'
    rw [hD, hψ x hx' hxF]
    exact (mem_Fd_iff φ hxF).mp hx
  obtain ⟨c, hc⟩ := RuRank3.titsA_sylow_five_overgroup hK25 hKidx hKtop hKD
  have hγcard : Nat.card (stabilizer (stabilizer G ω₀) γ) = 15600 := by
    rw [← Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hc,
      Subgroup.card_map_of_injective (MulAut.conj c).injective, RuRank3.card_ruE0]
  have hn2 : (orbit (stabilizer G ω₀) γ).ncard = 2304 := by
    have := horb γ
    rw [hγcard] at this
    omega
  have hL : RuRank3.IsL225Plus (stabilizer (stabilizer G ω₀) γ) := by
    have e1 : ↥RuRank3.ruE0 ≃* ↥(RuRank3.ruE0.map (MulAut.conj c).toMonoidHom) :=
      Subgroup.equivMapOfInjective _ _ (MulAut.conj c).injective
    have e2 : ↥(stabilizer (stabilizer G ω₀) γ) ≃*
        ↥((stabilizer (stabilizer G ω₀) γ).map ψ.toMonoidHom) :=
      Subgroup.equivMapOfInjective _ _ ψ.injective
    exact RuRank3.isL225Plus_ruE0.of_mulEquiv
      (e1.trans ((MulEquiv.subgroupCongr hc.symm).trans e2.symm))
  have hrank : Nat.card (orbitRel.Quotient (stabilizer G ω₀) (G ⧸ (M.F1 ⊔ M.F2))) = 3 := by
    refine J11.card_orbitRel_quotient_eq_three ![ω₀, δ, γ] ![1, 1755, 2304] (by decide) ?_
      (by rw [hΩ]; rfl)
    intro i
    fin_cases i
    · exact hn0
    · exact hn1
    · exact hn2
  exact RuRank3.IsRudvalisRank3.of_point (M.faithfulSMul_quotient φ) inferInstance ω₀ hrank
    ⟨ψ⟩ ⟨δ, hδcard, RuRank3.isSylowTwoParabolic_of_card ψ hδcard⟩ ⟨γ, hL⟩

end RuDataM

end CFSG.Quasithin.RuType
