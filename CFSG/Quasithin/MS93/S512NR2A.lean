module

public import CFSG.Quasithin.MS93.S512NQ
public import CFSG.Quasithin.MS93.S5B57

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S512N

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem commutator_conj_eq_one_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E₀ P₀ : Subgroup G} (hE₀M : E₀ ≤ M) (hE₀2 : IsPGroup 2 E₀) (hE₀O : ¬ E₀ ≤ pCoreOf 2 M)
    (hrel : (Subgroup.centralizer (E₀ : Set G)).relIndex (Uq M T L) ≤ 2 ^ k)
    (hP₀M : P₀ ≤ M) (hP₀2 : IsPGroup 2 P₀) (hPE : P₀ ≤ Subgroup.normalizer (E₀ : Set G))
    {e y u : G} (he : e ∈ E₀) (hy : y ∈ P₀) (hu : u ∈ Uq M T L) :
    ⁅e, y * u * y⁻¹ * u⁻¹⁆ = 1 := by
  have := S5B.charP_two_of_card hd.2.1
  obtain ⟨nv⟩ := hd.nonempty_natVec
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  obtain ⟨p, hp, hfix⟩ := (S5B.relIndex_centralizer_M h hd hE₀M hE₀2 hE₀O).2 hrel
  have hyM := hP₀M hy
  have heM := hE₀M he
  set Ē := (E₀.subgroupOf M).map a with hĒ
  have key : ∀ z ∈ P₀, ∀ hz : z ∈ M,
      Ē.map (MulAut.conj (a ⟨z, hz⟩)).toMonoidHom ≤ Ē := by
    rintro z hzP hzM _ ⟨_, ⟨e', he', rfl⟩, rfl⟩
    have hc : z * (e' : G) * z⁻¹ ∈ E₀ :=
      (Subgroup.mem_normalizer_iff.1 (hPE hzP) e').1 (Subgroup.mem_subgroupOf.1 he')
    refine ⟨⟨z, hzM⟩ * e' * ⟨z, hzM⟩⁻¹, Subgroup.mem_subgroupOf.2 hc, ?_⟩
    simp [map_mul, map_inv]
  have hyn : a ⟨y, hyM⟩ ∈ Subgroup.normalizer (Ē : Set (MSP.Sp4 F)) := by
    refine mem_normalizer_of_map_conj_le (key y hy hyM) ?_
    have := key y⁻¹ (inv_mem hy) (inv_mem hyM)
    rwa [show (⟨y⁻¹, inv_mem hyM⟩ : ↥M) = (⟨y, hyM⟩ : ↥M)⁻¹ from rfl, map_inv] at this
  have hys : a ⟨y, hyM⟩ ∈ MSP.stab p := by
    have := MSP.normalizer_le_stab_fixSp Ē hyn
    rwa [hfix, MSP.stab_perp] at this
  obtain ⟨n, hn⟩ := hP₀2 ⟨y, hy⟩
  have hn' : (a ⟨y, hyM⟩) ^ 2 ^ n = 1 := by
    have h1 : (⟨y, hyM⟩ : ↥M) ^ 2 ^ n = 1 := by
      apply Subtype.ext
      simpa using congrArg Subtype.val hn
    rw [← map_pow, h1, map_one]
  have hUn := le_normalizer_Uq (T := T) h.le_normalizer
  have hyu : y * u * y⁻¹ ∈ Uq M T L := (Subgroup.mem_normalizer_iff.1 (hUn hyM) u).1 hu
  have hx : y * u * y⁻¹ * u⁻¹ ∈ Uq M T L := mul_mem hyu (inv_mem hu)
  have hvx : nv.vec ⟨_, hx⟩ ∈ MSP.perp p := by
    have e1 : (⟨_, hx⟩ : ↥(Uq M T L)) = ⟨y * u * y⁻¹, hyu⟩ * (⟨u, hu⟩ : ↥(Uq M T L))⁻¹ := rfl
    rw [e1, S5.NatVec.vec_mul, S5.NatVec.vec_inv, S5.NatVec.vec_conj nv ⟨y, hyM⟩ ⟨u, hu⟩ hyu,
      MSP.mem_perp]
    intro v hv
    have hyv := mulVec_eq_of_mem_stab_point hn' hp hys hv
    rw [map_add, map_neg, ← hyv, MSP.form_mat, hyv, add_neg_cancel]
  have hev : MSP.mat (a ⟨e, heM⟩) *ᵥ nv.vec ⟨_, hx⟩ = nv.vec ⟨_, hx⟩ := by
    have h1 : nv.vec ⟨_, hx⟩ ∈ MSP.fixSp Ē := by
      rw [hfix]
      exact hvx
    exact (MSP.mem_fixSp.1 h1) _ ⟨⟨e, heM⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩
  have hex : e * (y * u * y⁻¹ * u⁻¹) * e⁻¹ ∈ Uq M T L :=
    (Subgroup.mem_normalizer_iff.1 (hUn heM) _).1 hx
  have hC : e * (y * u * y⁻¹ * u⁻¹) * e⁻¹ * (y * u * y⁻¹ * u⁻¹)⁻¹ ∈
      Subgroup.centralizer (L : Set G) := by
    have h0 : nv.vec (⟨_, hex⟩ * (⟨_, hx⟩ : ↥(Uq M T L))⁻¹) = 0 := by
      rw [S5.NatVec.vec_mul, S5.NatVec.vec_inv, S5.NatVec.vec_conj nv ⟨e, heM⟩ ⟨_, hx⟩ hex, hev,
        add_neg_cancel]
    exact (nv.vec_eq_zero_iff _).1 h0
  have h1 := hlift e heM _ hx hC
  rw [commutatorElement_def, h1, mul_inv_cancel]

theorem commutator_conj_eq_one_at (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {σ : Vtx (puAmalgam h.le)} (hσ : IsMVtx _ σ) {E P : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ stab _ σ) (hE2 : IsPGroup 2 E) (hEQ : ¬ E ≤ Qv _ σ)
    (hrel : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L σ) ≤ 2 ^ k)
    (hP : P ≤ stab _ σ) (hP2 : IsPGroup 2 P)
    (hPE : P ≤ Subgroup.normalizer (E : Set (puAmalgam h.le).Universal))
    {e y u : (puAmalgam h.le).Universal} (he : e ∈ E) (hy : y ∈ P)
    (hu : u ∈ S5.uSub h.le L σ) : ⁅e, y * u * y⁻¹ * u⁻¹⁆ = 1 := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hσ
  obtain ⟨E₀, hE₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g hE
  obtain ⟨P₀, hP₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g hP
  obtain ⟨hE₀2, hE₀O⟩ := S5B.isPGroup_not_le_of_smul h g hE₀M hE2 hEQ
  have hP₀2 : IsPGroup 2 P₀ := by
    have e1 : ↥P₀ ≃* ↥(imM h.le P₀) := by
      refine (Subgroup.subgroupOfEquivOfLe hP₀M).symm.trans ?_
      exact Subgroup.equivMapOfInjective _ _ (puAmalgam h.le).ofA_injective
    have e2 : ↥(imM h.le P₀) ≃* ↥((imM h.le P₀).map (MulAut.conj g).toMonoidHom) :=
      Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective
    exact hP2.of_equiv (e1.trans e2).symm
  rw [S5B.relIndex_centralizer_smul h g hE₀M] at hrel
  have hPE₀ : P₀ ≤ Subgroup.normalizer (E₀ : Set G) := by
    refine le_normalizer_of_imM h.le hE₀M hP₀M ?_
    rw [le_normalizer_map_conj_iff, map_conj_inv_map_conj] at hPE
    exact hPE
  obtain ⟨_, ⟨e₀, he₀, rfl⟩, rfl⟩ := he
  obtain ⟨_, ⟨y₀, hy₀, rfl⟩, rfl⟩ := hy
  rw [S5.uSub_smul h.le hLn, S5.uSub_baseA h] at hu
  obtain ⟨_, ⟨u₀, hu₀, rfl⟩, rfl⟩ := hu
  have key := commutator_conj_eq_one_M h hd hE₀M hE₀2 hE₀O hrel hP₀M hP₀2 hPE₀
    (Subgroup.mem_subgroupOf.1 he₀) (Subgroup.mem_subgroupOf.1 hy₀) (Subgroup.mem_subgroupOf.1 hu₀)
  have e1 : ⁅(e₀ : ↥M), (y₀ : ↥M) * u₀ * (y₀ : ↥M)⁻¹ * (u₀ : ↥M)⁻¹⁆ = 1 :=
    Subtype.ext key
  have e2 := congrArg ((MulAut.conj g).toMonoidHom.comp (puAmalgam h.le).ofA) e1
  simpa only [map_commutatorElement, map_mul, map_inv, map_one, MonoidHom.comp_apply] using e2

theorem critR_le_centralizer (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {ρ σ γ : Vtx (puAmalgam h.le)} (hσ : IsMVtx _ σ) (hσγ : (puAmalgam h.le).treeGraph.Adj σ γ)
    {V : Subgroup (puAmalgam h.le).Universal} (hZρ : ZM _ ρ ≤ V) (hVσ : V ≤ stab _ σ)
    (hV2 : IsPGroup 2 V) (hVQ : ¬ V ≤ Qv _ σ)
    (hrel : (Subgroup.centralizer (V : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L σ) ≤ 2 ^ k)
    (hQσ : Qv _ γ ≤ stab _ σ) (hQ2 : IsPGroup 2 (Qv _ γ))
    (hQV : Qv _ γ ≤ Subgroup.normalizer (V : Set (puAmalgam h.le).Universal))
    (hZγ : ZH _ γ ≤ Subgroup.centralizer (ZM _ ρ : Set (puAmalgam h.le).Universal)) :
    ⁅ZM _ ρ, ZM _ σ⁆ ≤ Subgroup.centralizer (Qv _ γ : Set (puAmalgam h.le).Universal) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hZσc : ZM _ σ ≤ Subgroup.centralizer (ZM _ σ : Set (puAmalgam h.le).Universal) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr (isElemAbelian_zm _ hyp hb0 hσ).1
  have hQσc : Qv _ σ ≤ Subgroup.centralizer (ZM _ σ : Set (puAmalgam h.le).Universal) :=
    Subgroup.le_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hσ)
  have hVT : ⁅V, Qv _ γ⁆ ≤ Qv _ σ :=
    commutator_le_qv_of_le_normalizer h hd hσ hVσ hV2 hVQ hrel hQσ hQ2 hQV
  have hUZ : S5.uSub h.le L σ ≤ ZM _ σ := S5B.uSub_le_zm h.le σ
  have hZn : ∀ x ∈ stab _ σ, ∀ y ∈ ZM _ σ, x * y * x⁻¹ ∈ ZM _ σ := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.1 (stab_le_normalizer_zm _ _ hx) y).1 hy
  have hcZ : ∀ z ∈ ZM _ ρ, ∀ d ∈ ZM _ σ, ⁅z, d⁆ ∈ ZM _ σ := by
    intro z hz d hd'
    rw [commutatorElement_def]
    exact mul_mem (hZn z (hVσ (hZρ hz)) d hd') (inv_mem hd')
  have core : ∀ z ∈ ZM _ ρ, ∀ u ∈ S5.uSub h.le L σ, ∀ t ∈ Qv _ γ,
      t * ⁅z, u⁆ * t⁻¹ = ⁅z, u⁆ := by
    intro z hz u hu t ht
    have hzV := hZρ hz
    have huZ := hUZ hu
    have hn : z⁻¹ * (t * z * t⁻¹) ∈ Qv _ σ := by
      have := hVT (Subgroup.commutator_mem_commutator (inv_mem hzV) ht)
      rw [commutatorElement_def, inv_inv] at this
      simpa [mul_assoc] using this
    have hw1 := commutator_conj_eq_one_at h hd hσ hVσ hV2 hVQ hrel hQσ hQ2 hQV hzV ht hu
    have hwZ : t * u * t⁻¹ * u⁻¹ ∈ ZM _ σ := mul_mem (hZn t (hQσ ht) u huZ) (inv_mem huZ)
    set n := z⁻¹ * (t * z * t⁻¹) with hndef
    set w := t * u * t⁻¹ * u⁻¹ with hwdef
    have hnw : n * w = w * n := (Subgroup.mem_centralizer_iff.1 (hQσc hn) w hwZ).symm
    have hnu : n * u = u * n := (Subgroup.mem_centralizer_iff.1 (hQσc hn) u huZ).symm
    have hzw : z * w = w * z := commutatorElement_eq_one_iff_mul_comm.1 hw1
    have hwc : w * ⁅z, u⁆ = ⁅z, u⁆ * w :=
      (Subgroup.mem_centralizer_iff.1 (hZσc (hcZ z hz u huZ)) w hwZ)
    have htz : t * z * t⁻¹ = z * n := by rw [hndef]; group
    have htu : t * u * t⁻¹ = w * u := by rw [hwdef]; group
    calc t * ⁅z, u⁆ * t⁻¹ = ⁅t * z * t⁻¹, t * u * t⁻¹⁆ := by
          simp only [commutatorElement_def]
          group
      _ = z * (n * w) * u * n⁻¹ * z⁻¹ * u⁻¹ * w⁻¹ := by
          rw [htz, htu, commutatorElement_def]
          group
      _ = z * w * (n * u) * n⁻¹ * z⁻¹ * u⁻¹ * w⁻¹ := by rw [hnw]; group
      _ = (z * w) * u * z⁻¹ * u⁻¹ * w⁻¹ := by rw [hnu]; group
      _ = w * ⁅z, u⁆ * w⁻¹ := by rw [hzw, commutatorElement_def]; group
      _ = ⁅z, u⁆ := by rw [hwc]; group
  let S : Subgroup (puAmalgam h.le).Universal :=
    { carrier := {d | d ∈ ZM _ σ ∧ ∀ z ∈ ZM _ ρ,
        ⁅z, d⁆ ∈ Subgroup.centralizer (Qv _ γ : Set (puAmalgam h.le).Universal)}
      one_mem' := ⟨one_mem _, fun z _ => by
        rw [commutatorElement_one_right]
        exact one_mem _⟩
      mul_mem' := fun {d d'} hd' hd'' => ⟨mul_mem hd'.1 hd''.1, fun z hz => by
        have e : ⁅z, d * d'⁆ = ⁅z, d⁆ * (d * ⁅z, d'⁆ * d⁻¹) := by
          simp only [commutatorElement_def]
          group
        have hc : d * ⁅z, d'⁆ * d⁻¹ = ⁅z, d'⁆ := by
          rw [Subgroup.mem_centralizer_iff.1 (hZσc (hcZ z hz d' hd''.1)) d hd'.1,
            mul_inv_cancel_right]
        rw [e, hc]
        exact mul_mem (hd'.2 z hz) (hd''.2 z hz)⟩
      inv_mem' := fun {d} hd' => ⟨inv_mem hd'.1, fun z hz => by
        have e : ⁅z, d⁻¹⁆ = d⁻¹ * ⁅z, d⁆⁻¹ * d := by
          simp only [commutatorElement_def]
          group
        have hc : d⁻¹ * ⁅z, d⁆⁻¹ * d = ⁅z, d⁆⁻¹ := by
          rw [mul_assoc, ← (Subgroup.mem_centralizer_iff.1 (hZσc (inv_mem (hcZ z hz d hd'.1))) d
            hd'.1), inv_mul_cancel_left]
        rw [e, hc]
        exact inv_mem (hd'.2 z hz)⟩ }
  have hS : ZM _ σ ≤ S := by
    rw [S5B.zm_eq_zh_sup_uSub h hσ hσγ]
    refine sup_le (fun d hd' => ⟨?_, fun z hz => ?_⟩) (fun u hu => ⟨hUZ hu, fun z hz => ?_⟩)
    · rw [S5B.zm_eq_zh_sup_uSub h hσ hσγ]
      exact Subgroup.mem_sup_left hd'
    · have : ⁅z, d⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
        (Subgroup.mem_centralizer_iff.1 (hZγ hd') z hz)
      rw [this]
      exact one_mem _
    · rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have := core z hz u hu t ht
      calc t * ⁅z, u⁆ = t * ⁅z, u⁆ * t⁻¹ * t := by group
        _ = ⁅z, u⁆ * t := by rw [this]
  rw [Subgroup.commutator_le]
  exact fun z hz d hd' => (hS hd').2 z hz

end S512N

end CFSG.Quasithin.MS93
