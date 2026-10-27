module

public import CFSG.Quasithin.MS93.S512TBad
public import CFSG.Quasithin.MS93.S5A53
public import CFSG.Quasithin.MS93.S5BL2

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S512H

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem le_centralizer_M_of_le_sup (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    (h32 : ⁅Xq M, L⁆ ≤ Uq M T L) (hZc : Zq M L ≤ Subgroup.centralizer (M : Set G))
    {R S : Subgroup G} (hRX : R ≤ Xq M) (hRn : M ≤ Subgroup.normalizer (R : Set G))
    (hSX : S ≤ Xq M) (hRS : R ≤ S ⊔ Zq M L) (hSc : Nat.card S < (2 ^ k) ^ 4) :
    R ≤ Subgroup.centralizer (M : Set G) := by
  obtain ⟨nv⟩ := S5.IsSp4Data.nonempty_natVec hd
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have hFq : Nat.card F = 2 ^ k := hd.nat_card_eq
  have hSN : S ≤ Subgroup.normalizer (Zq M L : Set G) :=
    S5.le_normalizer_of_commute fun s hs z hz => S5.commute_of_mem_Xq (hSX hs) hz.1
  have hclaim : ∀ u : ↥(Uq M T L), (u : G) ∈ R → nv.vec u = 0 := by
    by_contra hne
    push Not at hne
    obtain ⟨u₀, hu₀R, hu₀⟩ := hne
    let W : AddSubgroup (MSP.V4 F) :=
      { carrier := {w | ∃ u : ↥(Uq M T L), (u : G) ∈ R ∧ nv.vec u = w}
        add_mem' := by
          rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
          exact ⟨u * u', R.mul_mem hu hu', nv.vec_mul u u'⟩
        zero_mem' := ⟨1, R.one_mem, nv.vec_one⟩
        neg_mem' := by
          rintro _ ⟨u, hu, rfl⟩
          exact ⟨u⁻¹, R.inv_mem hu, nv.vec_inv u⟩ }
    have hinv : ∀ g : MSP.Sp4 F, ∀ v ∈ W, MSP.mat g *ᵥ v ∈ W := by
      rintro g _ ⟨u, huR, rfl⟩
      obtain ⟨m, rfl⟩ := hd.surj g
      have hu' : (m : G) * u * (m : G)⁻¹ ∈ Uq M T L :=
        (Subgroup.mem_normalizer_iff.1 (hUn m.2) u).1 u.2
      exact ⟨⟨_, hu'⟩, (Subgroup.mem_normalizer_iff.1 (hRn m.2) u).1 huR, nv.vec_conj m u hu'⟩
    have htop := S512T.eq_top_of_invariant hinv ⟨u₀, hu₀R, rfl⟩ hu₀
    have hsurj : Function.Surjective (fun s : ↥S => S5.uCoord nv (s : G)) := by
      intro w
      have hw : w ∈ W := by rw [htop]; exact AddSubgroup.mem_top w
      obtain ⟨u, huR, rfl⟩ := hw
      have huS : (u : G) ∈ ((S ⊔ Zq M L : Subgroup G) : Set G) := hRS huR
      rw [Subgroup.coe_mul_of_left_le_normalizer_right S _ hSN] at huS
      obtain ⟨s, hs, z, hz, hsz⟩ := huS
      refine ⟨⟨s, hs⟩, ?_⟩
      have e : s = (u : G) * z⁻¹ := by rw [← hsz, mul_inv_cancel_right]
      show S5.uCoord nv s = nv.vec u
      rw [e, S5.uCoord_mul nv u.2 ((Zq M L).inv_mem hz)]
    have h1 := Nat.card_le_card_of_surjective _ hsurj
    rw [MSP.card_V4, hFq] at h1
    omega
  have hW : R ⊓ Uq M T L ≤ Subgroup.centralizer (L : Set G) := by
    rintro x ⟨hxR, hxU⟩
    exact (nv.vec_eq_zero_iff ⟨x, hxU⟩).1 (hclaim ⟨x, hxU⟩ hxR)
  have hRL : ⁅R, L⁆ ≤ R ⊓ Uq M T L :=
    le_inf (commutator_le_left_of_le_normalizer (h.L_le.trans hRn))
      ((Subgroup.commutator_mono hRX le_rfl).trans h32)
  have hRL2 : ⁅R ⊓ Uq M T L, L⁆ ≤ ⊥ := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hxy : y * x = x * y := Subgroup.mem_centralizer_iff.1 (hW hx) y hy
    rw [commutatorElement_def, ← hxy, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hRL3 := S5B.commutator_le_of_perfect (U := (⊥ : Subgroup G)) h.perfect
    (Subgroup.le_normalizer_of_normal) (Subgroup.le_normalizer_of_normal) hRL hRL2
  have hRCL : R ≤ Subgroup.centralizer (L : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact le_bot_iff.1 hRL3
  exact (le_inf hRX hRCL).trans hZc

theorem le_stabCenter_of_le_sup (h32 : S32) (hq2 : S5B.Q2Cent) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {R S : Subgroup (puAmalgam h.le).Universal} (hRX : R ≤ XM _ (baseA (puAmalgam h.le)))
    (hRn : stab _ (baseA (puAmalgam h.le)) ≤ Subgroup.normalizer (R : Set _))
    (hSX : S ≤ XM _ (baseA (puAmalgam h.le))) (hRS : R ≤ S ⊔ imM h.le (Zq M L))
    (hSc : Nat.card S < (2 ^ k) ^ 4) : R ≤ stabCenter _ (baseA (puAmalgam h.le)) := by
  rw [S5B.xm_baseA_eq h] at hRX hSX
  obtain ⟨R₀, hR₀X, hR₀M, rfl⟩ := S5B.exists_eq_imM h.le hRX
  obtain ⟨S₀, hS₀X, hS₀M, rfl⟩ := S5B.exists_eq_imM h.le hSX
  have hZM : Zq M L ≤ M := inf_le_left.trans (Xq_le M)
  have hRn₀ : M ≤ Subgroup.normalizer (R₀ : Set G) := by
    rw [puAmalgam.stab_baseA] at hRn
    exact S512T.le_normalizer_of_imM h.le le_rfl hR₀M hRn
  have hRS₀ : R₀ ≤ S₀ ⊔ Zq M L := by
    rw [← S5B.imM_sup_of_le h.le hS₀M hZM] at hRS
    exact (imM_le_imM_iff h.le hR₀M).1 hRS
  rw [S5B.card_imM h.le hS₀M] at hSc
  have hZc := S5B.zq_le_centralizer hq2 h hmin hb hd
  have key := le_centralizer_M_of_le_sup h hd (h32 G M T L h).2.1 hZc hR₀X hRn₀ hS₀X hRS₀ hSc
  rw [S5B.stabCenter_baseA h.le]
  exact imM_mono h.le (le_inf hR₀M key)

theorem uq_le_sup_of_ne_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E E' : Subgroup G} (hEM : E ≤ M) (hE'M : E' ≤ M)
    (hrel : (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) = 2 ^ k)
    (hrel' : (Subgroup.centralizer (E' : Set G)).relIndex (Uq M T L) = 2 ^ k)
    (hne : Uq M T L ⊓ Subgroup.centralizer (E : Set G) ≠
      Uq M T L ⊓ Subgroup.centralizer (E' : Set G)) :
    Uq M T L ≤ (Uq M T L ⊓ Subgroup.centralizer (E : Set G)) ⊔
      (Uq M T L ⊓ Subgroup.centralizer (E' : Set G)) := by
  obtain ⟨nv⟩ := S5.IsSp4Data.nonempty_natVec hd
  obtain ⟨-, hUL, hlift⟩ := sp4Lift_holds G M T L h k F _ _ a hd
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  obtain ⟨p, hp, -, hfix, -⟩ := S510.exists_point_of_relIndex h hd hEM hrel
  obtain ⟨p', hp', -, hfix', -⟩ := S510.exists_point_of_relIndex h hd hE'M hrel'
  have hmemE : ∀ u : ↥(Uq M T L),
      (u : G) ∈ Subgroup.centralizer (E : Set G) ↔ nv.vec u ∈ MSP.perp p := fun u => by
    rw [← hfix]
    exact nv.mem_centralizer_iff_vec_mem_fixSp hUn hlift hEM u
  have hmemE' : ∀ u : ↥(Uq M T L),
      (u : G) ∈ Subgroup.centralizer (E' : Set G) ↔ nv.vec u ∈ MSP.perp p' := fun u => by
    rw [← hfix']
    exact nv.mem_centralizer_iff_vec_mem_fixSp hUn hlift hE'M u
  have hpp : MSP.perp p ≠ MSP.perp p' := by
    intro he
    apply hne
    ext x
    constructor
    · rintro ⟨hxU, hx⟩
      exact ⟨hxU, (hmemE' ⟨x, hxU⟩).2 (he ▸ (hmemE ⟨x, hxU⟩).1 hx)⟩
    · rintro ⟨hxU, hx⟩
      exact ⟨hxU, (hmemE ⟨x, hxU⟩).2 (he ▸ (hmemE' ⟨x, hxU⟩).1 hx)⟩
  have h3 : Module.finrank F (MSP.perp p) = 3 := by
    have := MSP.finrank_perp p
    rw [show Module.finrank F p = 1 from hp] at this
    omega
  have h3' : Module.finrank F (MSP.perp p') = 3 := by
    have := MSP.finrank_perp p'
    rw [show Module.finrank F p' = 1 from hp'] at this
    omega
  have hsup : MSP.perp p ⊔ MSP.perp p' = ⊤ := by
    have hlt : MSP.perp p < MSP.perp p ⊔ MSP.perp p' := by
      refine lt_of_le_of_ne le_sup_left fun he => hpp ?_
      have hle : MSP.perp p' ≤ MSP.perp p := he ▸ le_sup_right
      exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [h3, h3'])).symm
    have h4 := Submodule.finrank_lt_finrank_of_lt hlt
    have h5 := Submodule.finrank_le (MSP.perp p ⊔ MSP.perp p')
    have h6 : Module.finrank F (MSP.V4 F) = 4 := by simp
    apply Submodule.eq_top_of_finrank_eq
    omega
  intro u hu
  have hv : nv.vec ⟨u, hu⟩ ∈ MSP.perp p ⊔ MSP.perp p' := by
    rw [hsup]
    exact Submodule.mem_top
  obtain ⟨v₁, hv₁, v₂, hv₂, hsum⟩ := Submodule.mem_sup.1 hv
  obtain ⟨u₁, hu₁⟩ := nv.surj (Multiplicative.ofAdd v₁)
  obtain ⟨u₂, hu₂⟩ := nv.surj (Multiplicative.ofAdd v₂)
  have hvu₁ : nv.vec u₁ = v₁ := by rw [S5.NatVec.vec, hu₁]; rfl
  have hvu₂ : nv.vec u₂ = v₂ := by rw [S5.NatVec.vec, hu₂]; rfl
  set u₀ : ↥(Uq M T L) := ⟨u, hu⟩ * u₂⁻¹ * u₁⁻¹ with hu₀def
  have hu₀ : nv.vec u₀ = 0 := by
    rw [hu₀def, nv.vec_mul, nv.vec_mul, nv.vec_inv, nv.vec_inv, hvu₁, hvu₂, ← hsum]
    abel
  have hu₀M : (u₀ : G) ∈ Uq M T L ⊓ Subgroup.centralizer (M : Set G) := by
    rw [← hUL]
    exact ⟨u₀.2, (nv.vec_eq_zero_iff u₀).1 hu₀⟩
  have hu₀E : (u₀ : G) ∈ Subgroup.centralizer (E : Set G) := Subgroup.centralizer_le hEM hu₀M.2
  have e : u = (u₀ : G) * u₁ * u₂ := by
    rw [hu₀def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact mul_mem (mul_mem (Subgroup.mem_sup_left ⟨u₀.2, hu₀E⟩)
    (Subgroup.mem_sup_left ⟨u₁.2, (hmemE u₁).2 (hvu₁ ▸ hv₁)⟩))
    (Subgroup.mem_sup_right ⟨u₂.2, (hmemE' u₂).2 (hvu₂ ▸ hv₂)⟩)

theorem uSub_le_sup_of_ne (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) {E E' : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ stab _ δ) (hE' : E' ≤ stab _ δ)
    (hrel : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L δ) = 2 ^ k)
    (hrel' : (Subgroup.centralizer (E' : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L δ) = 2 ^ k)
    (hne : S5.uSub h.le L δ ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) ≠
      S5.uSub h.le L δ ⊓ Subgroup.centralizer (E' : Set (puAmalgam h.le).Universal)) :
    S5.uSub h.le L δ ≤
      (S5.uSub h.le L δ ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)) ⊔
        (S5.uSub h.le L δ ⊓ Subgroup.centralizer (E' : Set (puAmalgam h.le).Universal)) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hδ
  obtain ⟨E₀, hE₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g hE
  obtain ⟨E₁, hE₁M, rfl⟩ := S5B.exists_eq_map_imM h.le g hE'
  have hU : S5.uSub h.le L (g • baseA (puAmalgam h.le)) =
      (imM h.le (Uq M T L)).map (MulAut.conj g).toMonoidHom := by
    rw [S5B.uSub_smul h.le hLn, S5B.uSub_baseA h]
  rw [S5B.relIndex_centralizer_smul h g hE₀M] at hrel
  rw [S5B.relIndex_centralizer_smul h g hE₁M] at hrel'
  rw [S5B.uSub_inf_centralizer_smul h g hE₀M, S5B.uSub_inf_centralizer_smul h g hE₁M] at hne ⊢
  have hne₀ : Uq M T L ⊓ Subgroup.centralizer (E₀ : Set G) ≠
      Uq M T L ⊓ Subgroup.centralizer (E₁ : Set G) := fun he => hne (by rw [he])
  have key := uq_le_sup_of_ne_M h hd hE₀M hE₁M hrel hrel' hne₀
  rw [hU, ← Subgroup.map_sup, ← S5B.imM_sup_of_le h.le (inf_le_left.trans hUM)
    (inf_le_left.trans hUM)]
  exact Subgroup.map_mono (imM_mono h.le key)

end S512H

end CFSG.Quasithin.MS93
