module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35E10C
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35E10E

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.E10

open S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem lam_nonempty (hS : Sit H M S) (hLP : ClaimLP H M) (h9 : Claim9 H M)
    (h8a : Claim8a H M) (h7 : Claim7s H M) (hT : ClaimT H M)
    (hsec : ∀ β : Geo H M, vtype β = false → IsSec (stab β) (Vn β) (Wb β)) :
    ∃ δ δ' : Geo H M, Lam δ δ' := by
  by_contra hcon
  have hΛ : ∀ δ δ' : Geo H M, S34.PD δ δ' → Zv δ ≤ Vn δ' := fun δ δ' hpd => by
    by_contra h
    exact hcon ⟨δ, δ', hpd, h⟩
  obtain ⟨β, α', hp, hTr⟩ := hLP
  obtain ⟨m, γ', hm, hγ, h1, h2⟩ := exists_geodesic hS hp.dist_eq
  have hb : Back H M β α' m γ' := ⟨hm, hγ, h1, h2⟩
  obtain ⟨α, hα, hαZ⟩ := exists_nbr_Zv_not_le hp
  have hWQ := Wl_le_Qv_of_lam_empty hS hΛ hp hb hα hαZ
  obtain ⟨A, B, hA, hB, hAB, hVA, hW8, hZB⟩ := h8a β α' hp hTr
  have hBQ : B ≤ Qv β := by
    by_cases hQ : Vn α' ≤ Qv β
    · exact hB.trans hQ
    · have hpd : S34.PD α' β :=
        ⟨hp.vδ', hp.vδ, by rw [CosetGeom.dist_comm]; exact hp.dist_eq, hQ⟩
      exact B_le_Qv hS h7 h9 (hsec β hp.vδ) hp hb (hΛ α' β hpd) hB hW8
  obtain ⟨x, hxB, hxQ⟩ := exists_not_mem_Qv hS (hZB α hα hαZ)
  have hxα : x ∈ stab α := Qv_le_stab hS hα (hBQ hxB)
  have hvβ := hp.vδ
  refine final_contra hS hT hp hb hα hWQ hxα hxQ fun e he => ?_
  have he' : e ∈ Wb β ⊓ stab α' := ⟨Wl_le_Wb hS hvβ hα he.1, he.2⟩
  have h3 := hW8 (Subgroup.commutator_mem_commutator he' hxB)
  have h4 : ⁅Vn β, B⁆ ≤ Zv β :=
    (Subgroup.commutator_mono le_rfl hBQ).trans (comm_Vn_Qv hS hvβ).le
  have e1 : x * e * x⁻¹ * e⁻¹ = ⁅e, x⁆⁻¹ := by rw [commutatorElement_def]; group
  rw [e1]
  exact (Zv α' ⊔ Zv β).inv_mem (sup_le_sup_left h4 _ h3)

theorem lam_symm (hS : Sit H M S) (hR : ClaimR H M) (h9 : Claim9 H M) (h8a : Claim8a H M)
    (h7 : Claim7s H M) (h16 : Claim16a H M)
    (hsec : ∀ β : Geo H M, vtype β = false → IsSec (stab β) (Vn β) (Wb β))
    {β α' : Geo H M} (hl : Lam β α') : Lam α' β := by
  obtain ⟨hp, hZβ⟩ := hl
  obtain ⟨m, γ', hm, hγ, h1, h2⟩ := exists_geodesic hS hp.dist_eq
  have hb : Back H M β α' m γ' := ⟨hm, hγ, h1, h2⟩
  have hvβ := hp.vδ
  have hQ : ¬ Vn α' ≤ Qv β := by
    intro hle
    obtain ⟨hne, -, -⟩ := hR β α' m γ' hp hb
    have h1 : ⁅Vn β, Vn α'⁆ ≤ Zv β :=
      (Subgroup.commutator_mono le_rfl hle).trans (comm_Vn_Qv hS hvβ).le
    have h2 : Zv β ≤ ⁅Vn β, Vn α'⁆ := le_of_ne_bot (hS.cardZ5 β hvβ) h1 hne
    exact hZβ (h2.trans ((PD_comm_le hS hp).trans inf_le_right))
  have hpd : S34.PD α' β :=
    ⟨hp.vδ', hvβ, by rw [CosetGeom.dist_comm]; exact hp.dist_eq, hQ⟩
  refine ⟨hpd, fun hZα' => ?_⟩
  obtain ⟨α, hα, hαZ⟩ := exists_nbr_Zv_not_le hp
  obtain ⟨A, B, hA, hB, hAB, hVA, hW8, hZB⟩ := h8a β α' hp (h16 β α' ⟨hp, hZβ⟩)
  have hBQ := B_le_Qv hS h7 h9 (hsec β hvβ) hp hb hZα' hB hW8
  have hne := hZB α hα hαZ
  have hle1 : ⁅B, Zv α⁆ ≤ Zv β := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono (Zv_le_Vn hα) hBQ).trans (comm_Vn_Qv hS hvβ).le
  have hle2 : Zv β ≤ ⁅B, Zv α⁆ := le_of_ne_bot (hS.cardZ5 β hvβ) hle1 hne
  have hle3 : ⁅B, Zv α⁆ ≤ Vn α' := by
    rw [Subgroup.commutator_le]
    intro b hb' z hz
    have hzs : z ∈ stab α' := (PD_Vn_le_stab hS hp).1 (Zv_le_Vn hα hz)
    have h : z * b⁻¹ * z⁻¹ ∈ Vn α' :=
      (Subgroup.mem_normalizer_iff.mp (Vn_normal α' hzs) _).mp ((Vn α').inv_mem (hB hb'))
    have e : ⁅b, z⁆ = b * (z * b⁻¹ * z⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact (Vn α').mul_mem (hB hb') h
  exact hZβ (hle2.trans hle3)

theorem claim10 (hS : Sit H M S) (hclaimR : ClaimR H M) (hLP : ClaimLP H M) (h9 : Claim9 H M)
    (h8a : Claim8a H M) (h7 : Claim7s H M) (hT : ClaimT H M) (h16 : Claim16a H M)
    (hsec : ∀ β : Geo H M, vtype β = false → IsSec (stab β) (Vn β) (Wb β)) : Claim10 H M :=
  ⟨lam_nonempty hS hLP h9 h8a h7 hT hsec, fun _ _ hl =>
    lam_symm hS hclaimR h9 h8a h7 h16 hsec hl⟩

end S35.E10

end F53.Stellmacher

end CFSG.Quasithin
