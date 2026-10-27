module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.ZvEdgeCentralizer
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.S3Vertex
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS3L30
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModSecBase

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

open CFSG.Quasithin CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom CFSG.LieType.BorelTits
  CFSG.Quasithin.F53Mod Equiv

variable {G : Type} [Group G] [Finite G]

theorem edge_image_card_two {H M S : Subgroup G} (hA : F53Amalgam H M S) {α β : Geo H M}
    {ψ : ↥(stab α) →* Perm (Fin 3)} (hs : Function.Surjective ψ)
    (hker : ∀ x : ↥(stab α), ψ x = 1 ↔ (x : G) ∈ Qv α) (hβ : β ∈ nbrs α) :
    Nat.card (((stab α ⊓ stab β).subgroupOf (stab α)).map ψ) = 2 := by
  set E' := (stab α ⊓ stab β).subgroupOf (stab α) with hE'
  have hkerE : ψ.ker ≤ E' := fun x hx => Qv_le_edge hA hβ ((hker x).mp hx)
  have h2 : Nat.card (E'.map ψ) ≤ 2 :=
    perm3_card_le_two_of_isPGroup _ (isPGroup_map_subgroupOf ψ (sylow_stab_inf_left hA hβ).2.1)
  have hidx : (E'.map ψ).index = E'.index := Subgroup.index_map_eq E' hs hkerE
  have hodd : ¬ 2 ∣ E'.index := (sylow_stab_inf_left hA hβ).2.2
  have h6 := (E'.map ψ).card_mul_index
  rw [card_perm3] at h6
  rw [hidx] at h6
  have hpos : 0 < Nat.card (E'.map ψ) := Nat.card_pos
  have h12 : Nat.card (E'.map ψ) = 1 ∨ Nat.card (E'.map ψ) = 2 := by omega
  rcases h12 with h | h
  · rw [h] at h6; omega
  · exact h

theorem mem_edge_of_map_mem {H M S : Subgroup G} (hA : F53Amalgam H M S) {α β : Geo H M}
    {ψ : ↥(stab α) →* Perm (Fin 3)}
    (hker : ∀ x : ↥(stab α), ψ x = 1 ↔ (x : G) ∈ Qv α) (hβ : β ∈ nbrs α)
    {x : ↥(stab α)} (hx : ψ x ∈ ((stab α ⊓ stab β).subgroupOf (stab α)).map ψ) :
    (x : G) ∈ stab α ⊓ stab β := by
  obtain ⟨y, hy, hxy⟩ := hx
  have hy' : (y : G) ∈ stab α ⊓ stab β := Subgroup.mem_subgroupOf.mp hy
  have h1 : ψ (y⁻¹ * x) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
  have h2 : ((y⁻¹ * x : ↥(stab α)) : G) ∈ stab α ⊓ stab β :=
    Qv_le_edge hA hβ ((hker _).mp h1)
  have h3 : (x : G) = (y : G) * ((y⁻¹ * x : ↥(stab α)) : G) := by simp
  rw [h3]
  exact (stab α ⊓ stab β).mul_mem hy' h2

theorem perm3_conj_swap (t : Perm (Fin 3)) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    ∃ σ : Perm (Fin 3), σ * t * σ⁻¹ = swap 0 1 := by
  have key : ∀ u : Perm (Fin 3), u ≠ 1 → u ^ 2 = 1 →
      ∃ σ : Perm (Fin 3), σ * u * σ⁻¹ = swap 0 1 := by decide +kernel
  exact key t ht ht2

theorem exists_conj_mem_S3Syl_iff (K : Subgroup (Perm (Fin 3))) (hK : IsPGroup 2 K)
    (h2 : Nat.card K = 2) :
    ∃ σ : Perm (Fin 3), ∀ y : Perm (Fin 3), y ∈ K ↔ σ * y * σ⁻¹ ∈ S3Syl := by
  have hne : K ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨⟨t, htK⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hKt : K = Subgroup.zpowers t :=
    (perm3_eq_of_le_of_isPGroup _ K hK (Subgroup.zpowers_le.mpr htK)
      (fun h => ht1' (Subgroup.zpowers_eq_bot.mp h))).symm
  have ht2 : t ^ 2 = 1 := by
    have h := orderOf_dvd_natCard (⟨t, htK⟩ : K)
    rw [h2, Subgroup.orderOf_mk] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  obtain ⟨σ, hσ⟩ := perm3_conj_swap t ht1' ht2
  refine ⟨σ, fun y => ?_⟩
  rw [hKt, S3Syl, ← hσ, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by rw [conj_zpow]⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [conj_zpow] at hk
    have := congrArg (fun z => σ⁻¹ * z * σ) hk
    simpa using this

theorem card_Zv_eq_sq {H M S : Subgroup G} (hA : F53Amalgam H M S) {α β : Geo H M}
    (hα : vtype α = true) (hαβ : (graph (H ⊔ M) H M).Adj α β)
    (hz : Zv β ≤ centerOf (stab β)) :
    Nat.card (Zv α) = Nat.card (Zv β) ^ 2 := by
  have hadj : α ∈ nbrs β := hαβ.symm
  have hbadj : β ∈ nbrs α := hαβ
  have hAeq : Zv α ⊓ Subgroup.centralizer ((stab α ⊓ stab β : Subgroup G) : Set G) = Zv β :=
    Zv_inf_centralizer_edge_eq hA hαβ hz
  have hsub : Zv β ≤ Subgroup.centralizer ((stab α ⊓ stab β : Subgroup G) : Set G) := by
    rw [← hAeq]; exact inf_le_right
  have hβα : Zv β ≤ Zv α := by rw [← hAeq]; exact inf_le_left
  have hcen : centerOf (stab α) = ⊥ := centerOf_eq_bot_of_Zv_central hA hadj hz
  have hZα : Zv α ≤ stab α := fun z hz' => pCoreOf_le 2 _ (Zv_le_Qv hA α hz')
  obtain ⟨ψ, hsurj, hker⟩ := exists_quotHom_true hA hα
  obtain ⟨σ, hσ⟩ := exists_conj_mem_S3Syl_iff
    (((stab α ⊓ stab β).subgroupOf (stab α)).map ψ)
    (isPGroup_map_subgroupOf ψ (sylow_stab_inf_left hA hbadj).2.1)
    (edge_image_card_two hA hsurj hker hbadj)
  let θ : ↥(stab α) →* Perm (Fin 3) := (MulAut.conj σ).toMonoidHom.comp ψ
  have hθ : Function.Surjective θ := by
    intro b
    obtain ⟨x, hx⟩ := hsurj (σ⁻¹ * b * σ)
    exact ⟨x, by show σ * ψ x * σ⁻¹ = b; rw [hx]; group⟩
  have hθapp : ∀ h : ↥(stab α), θ h = σ * ψ h * σ⁻¹ := fun h => rfl
  have hchar : ∀ h : ↥(stab α), θ h ∈ S3Syl ↔ (h : G) ∈ stab α ⊓ stab β := by
    intro h
    rw [hθapp, ← hσ]
    exact ⟨fun hh => mem_edge_of_map_mem hA hker hbadj hh,
      fun hh => ⟨h, Subgroup.mem_subgroupOf.mpr hh, rfl⟩⟩
  have hnorm : (stab α) ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    intro g _
    exact Subgroup.mem_normalizer_iff.mpr (fun h => by simp)
  have hsec : IsSec (stab α) ⊥ (Zv α) :=
    { le := bot_le
      normN := stab_le_normalizer_Zv hA α
      normL := hnorm
      comm := fun x hx y hy => by
        have hc := (isElemAbelian_Zv hA α).1
        have hxy : x * y = y * x := by
          have := hc.is_comm.comm (⟨x, hx⟩ : Zv α) ⟨y, hy⟩
          exact congrArg Subtype.val this
        rw [hxy]
        simp
      sq := fun x hx => by
        have h1 : x ^ 2 = 1 := (isElemAbelian_Zv hA α).2 x hx
        rw [h1]
        exact (⊥ : Subgroup G).one_mem }
  have hk : θ.ker ≤ (cSecIn (stab α) ⊥ (Zv α)).subgroupOf (stab α) := by
    intro x hx
    have hψ : ψ x = 1 := by
      have h1 : σ * ψ x * σ⁻¹ = 1 := hx
      have h2 : σ * ψ x * σ⁻¹ = σ * 1 * σ⁻¹ := by rw [h1]; simp
      simpa using h2
    have hxC : (x : G) ∈ Subgroup.centralizer (Zv α : Set G) :=
      Qv_le_centralizer_Zv hA α ((hker x).mp hψ)
    rw [Subgroup.mem_subgroupOf, mem_cSecIn_iff hnorm]
    refine ⟨x.2, fun z hz => ?_⟩
    rw [Subgroup.mem_bot]
    have h := Subgroup.mem_centralizer_iff.mp hxC z hz
    rw [← h]
    group
  set M := secModule hsec θ hθ hk with hMdef
  let π : ↥(Zv α) →* M.W := hsec.proj
  have hπsurj : Function.Surjective π := fun w => hsec.proj_surjective w
  have hqinj : Function.Injective π := by
    intro x y h
    have h1 : (x : G)⁻¹ * (y : G) = 1 := Subgroup.mem_bot.mp ((hsec.proj_eq_proj_iff x y).mp h)
    exact Subtype.ext (inv_mul_eq_one.mp h1)
  have hbot : (⊥ : Subgroup G).subgroupOf (Zv α) = ⊥ := by
    ext x
    simp
  have hMW : Nat.card M.W = Nat.card (Zv α) := by
    show Nat.card (↥(Zv α) ⧸ (⊥ : Subgroup G).subgroupOf (Zv α)) = _
    rw [hbot]
    exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
  have hact : ∀ (h : ↥(stab α)) (x : ↥(Zv α)),
      M.act (θ h) (π x) = π (hsec.conjN h x) :=
    fun h x => secModule_act_proj hsec θ hθ hk h x
  have hconj : ∀ (h : ↥(stab α)) (x : ↥(Zv α)),
      ((hsec.conjN h x : ↥(Zv α)) : G) = (h : G) * (x : G) * (h : G)⁻¹ :=
    fun h x => rfl
  have hfix : ∀ (B : Subgroup (Perm (Fin 3))) (x : ↥(Zv α)),
      (∀ b ∈ B, M.act b (π x) = π x) ↔
        ∀ h : ↥(stab α), θ h ∈ B → (h : G) * (x : G) * (h : G)⁻¹ = (x : G) := by
    intro B x
    constructor
    · intro hB h hhB
      have h0 : π (hsec.conjN h x) = π x := (hact h x).symm.trans (hB _ hhB)
      have h1 : (x : G)⁻¹ * ((hsec.conjN h x : ↥(Zv α)) : G) ∈ (⊥ : Subgroup G) :=
        (hsec.proj_eq_proj_iff x (hsec.conjN h x)).mp h0.symm
      rw [hconj] at h1
      exact (inv_mul_eq_one.mp (Subgroup.mem_bot.mp h1)).symm
    · intro hh b hb
      obtain ⟨h, rfl⟩ := hθ b
      rw [hact]
      refine congrArg π (Subtype.ext ?_)
      rw [hconj, hh h hb]
  have hY : fixW M ⊤ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro w hw
    obtain ⟨x, rfl⟩ := hπsurj w
    have hc := (hfix ⊤ x).mp hw
    have hcent : (x : G) ∈ centerOf (stab α) := by
      refine Subgroup.mem_inf.mpr ⟨hZα x.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
      have := hc ⟨g, hg⟩ (Subgroup.mem_top _)
      exact mul_inv_eq_iff_eq_mul.mp this
    rw [hcen] at hcent
    exact (hsec.proj_eq_one_iff x).mpr hcent
  have hfixS3 : fixW M S3Syl = ((Zv β).subgroupOf (Zv α)).map π := by
    ext w
    obtain ⟨x, rfl⟩ := hπsurj w
    rw [Subgroup.mem_map]
    constructor
    · intro hw
      have hc := (hfix S3Syl x).mp hw
      have hxC : (x : G) ∈ Subgroup.centralizer ((stab α ⊓ stab β : Subgroup G) : Set G) := by
        refine Subgroup.mem_centralizer_iff.mpr fun g hg => ?_
        have hg' : g ∈ stab α ⊓ stab β := hg
        have hgα : g ∈ stab α := (Subgroup.mem_inf.mp hg').1
        have := hc ⟨g, hgα⟩ ((hchar ⟨g, hgα⟩).mpr hg')
        exact mul_inv_eq_iff_eq_mul.mp this
      have hxZβ : (x : G) ∈ Zv β := by
        rw [← hAeq]
        exact Subgroup.mem_inf.mpr ⟨x.2, hxC⟩
      exact ⟨x, Subgroup.mem_subgroupOf.mpr hxZβ, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have hyx' : y = x := hqinj hyx
      have hyβ : (y : G) ∈ Zv β := Subgroup.mem_subgroupOf.mp hy
      rw [← hyx']
      refine (hfix S3Syl y).mpr ?_
      intro h hh
      have hhE : (h : G) ∈ stab α ⊓ stab β := (hchar h).mp hh
      rw [Subgroup.mem_centralizer_iff.mp (hsub hyβ) (h : G) hhE, mul_inv_cancel_right]
  have hfixcard : Nat.card (fixW M S3Syl) = Nat.card (Zv β) := by
    rw [hfixS3, Subgroup.card_map_of_injective hqinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hβα).toEquiv
  obtain ⟨-, hsq⟩ := s3_card_eq_sq M hY
  rw [← hMW, hsq, hfixcard]

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

end
