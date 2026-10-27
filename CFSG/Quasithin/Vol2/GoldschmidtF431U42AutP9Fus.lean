module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP9Sur
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP9Cls
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP9Mod

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45 repL_x)

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section Fus

variable (c : AutCtx G M₁ M₂ z)

theorem decomp_G {l : PL} (hl : l ∈ Thl)
    (h : ∃ a ∈ Bl1, a ≠ idL ∧ ∃ b ∈ Bl2, b ≠ idL ∧ comp a b = l) :
    ∃ a₁ ∈ c.iso.imgG B1h, a₁ ≠ 1 ∧ ∃ b₁ ∈ c.iso.imgG B2h, b₁ ≠ 1 ∧
      c.iso.toG (eltB l) = a₁ * b₁ := by
  obtain ⟨aL, haL, haL1, bL, hbL, hbL1, hab⟩ := h
  have haT : aL ∈ Thl := Bl_thl.1 aL haL
  have hbT : bL ∈ Thl := Bl_thl.2 bL hbL
  have hne : ∀ {m : PL}, m ∈ Thl → m ≠ idL → c.iso.toG (eltB m) ≠ 1 := by
    intro m hm hm1 h
    have h0 : eltB m = 1 := c.iso.toG_injective (h.trans c.iso.toG_one.symm)
    have h1 : ((eltB m : Bh) : Ah) = 1 := by rw [h0]; rfl
    exact hm1 (repL_unique (repL_eltB hm) (by rw [h1]; exact repL_one 45))
  refine ⟨c.iso.toG (eltB aL), c.iso.mem_imgG.2 ⟨eltB aL, ⟨aL, haL, repL_eltB haT⟩, rfl⟩,
    hne haT haL1, c.iso.toG (eltB bL),
    c.iso.mem_imgG.2 ⟨eltB bL, ⟨bL, hbL, repL_eltB hbT⟩, rfl⟩, hne hbT hbL1, ?_⟩
  rw [← AutIso.toG_mul]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  exact eq_of_repL (repL_eltB hl) (by rw [← hab]; exact repL_mul (repL_eltB haT) (repL_eltB hbT))

section Act

variable (hZ : ZStmt c) (hT₀G : IsSylowTwoOf (c.iso.imgG That) ⊤)

include hZ hT₀G

theorem exists_conj_z_Fz :
    ∃ n ∈ Subgroup.normalizer (c.iso.imgG A2h : Set G), n * z * n⁻¹ = c.iso.toG fhB * z := by
  obtain ⟨-, -, -, -, hdec, hxA, hxZ, heA, heZ, -⟩ := P9_check
  have hxT : xL ∈ Thl := A2_check.2.2.2.1 xL hxA
  have heT : comp fhatL xL ∈ Thl := A2_check.2.2.2.1 _ heA
  obtain ⟨a₁, ha₁, ha₁1, b₁, hb₁, hb₁1, h₁⟩ := decomp_G c hxT (hdec xL hxA hxZ)
  obtain ⟨a₂, ha₂, ha₂1, b₂, hb₂, hb₂1, h₂⟩ := decomp_G c heT (hdec _ heA heZ)
  have hx : eltB xL = xB := (eltB_eq_of_rep hxT (show RepL xL ((xB : Ah) : P45) from repL_x)).symm
  have he : eltB (comp fhatL xL) = e0B :=
    (eltB_eq_of_rep heT (show RepL (comp fhatL xL) ((e0B : Ah) : P45) from
      repL_mul repL_fhat repL_x)).symm
  rw [hx, c.iso.toG_xB c.z2 c.z1 c.zc] at h₁
  have h3 : c.iso.toG e0B = c.iso.toG fhB * z := by
    show c.iso.toG (fhB * xB) = _
    rw [AutIso.toG_mul, c.iso.toG_xB c.z2 c.z1 c.zc]
  rw [he, h3] at h₂
  obtain ⟨n, hn, hna, hnb⟩ := normalizer_A2_act c hZ hT₀G ha₁ ha₁1 ha₂ ha₂1 hb₁ hb₁1 hb₂ hb₂1
  refine ⟨n, hn, ?_⟩
  calc n * z * n⁻¹ = n * (a₁ * b₁) * n⁻¹ := by rw [← h₁]
    _ = (n * a₁ * n⁻¹) * (n * b₁ * n⁻¹) := by group
    _ = a₂ * b₂ := by rw [hna, hnb]
    _ = c.iso.toG fhB * z := h₂.symm

theorem exists_conj_F_yt :
    ∃ n ∈ Subgroup.normalizer (c.iso.imgG A2h : Set G),
      n * c.iso.toG fhB * n⁻¹ = c.iso.toG (eltB lt2) := by
  obtain ⟨hfB, hltB, hlt1, -, hdec, hxA, hxZ, -⟩ := P9_check
  have hxT : xL ∈ Thl := A2_check.2.2.2.1 xL hxA
  obtain ⟨a₁, ha₁, ha₁1, b₁, hb₁, hb₁1, -⟩ := decomp_G c hxT (hdec xL hxA hxZ)
  have hfT : fhatL ∈ Thl := Bl_thl.2 fhatL hfB
  have hltT : lt2 ∈ Thl := Bl_thl.2 lt2 hltB
  have hF : c.iso.toG fhB ∈ c.iso.imgG B2h :=
    c.iso.mem_imgG.2 ⟨fhB, ⟨fhatL, hfB, repL_fhat⟩, rfl⟩
  have hF1 : c.iso.toG fhB ≠ 1 := F_ne_one c.iso
  have hy : c.iso.toG (eltB lt2) ∈ c.iso.imgG B2h :=
    c.iso.mem_imgG.2 ⟨eltB lt2, ⟨lt2, hltB, repL_eltB hltT⟩, rfl⟩
  have hy1 : c.iso.toG (eltB lt2) ≠ 1 := by
    intro h
    have h0 : eltB lt2 = 1 := c.iso.toG_injective (h.trans c.iso.toG_one.symm)
    have h1 : ((eltB lt2 : Bh) : Ah) = 1 := by rw [h0]; rfl
    exact hlt1 (repL_unique (repL_eltB hltT) (by rw [h1]; exact repL_one 45))
  obtain ⟨n, hn, -, hnb⟩ := normalizer_A2_act c hZ hT₀G ha₁ ha₁1 ha₁ ha₁1 hF hF1 hy hy1
  exact ⟨n, hn, hnb⟩

end Act

theorem yt_conj_t0 :
    ∃ m ∈ M₁ ⊔ M₂, m * c.iso.toG (eltB lt2) * m⁻¹ = c.iso.toG t0B := by
  obtain ⟨-, hltB, hlt1, ⟨k, hk, hkl, hkt⟩, -⟩ := P9_check
  have hlA : lt2 ∈ Al2 := Bl_check.2.2.2.1 lt2 hltB
  obtain ⟨hT, hsq, h1⟩ := eltB_inv_A2 hlA hlt1
  obtain ⟨g, hg, hgeq⟩ := inv_type_idx hT (congrArg (fun x : Bh => (x : Ah)) hsq) h1 hk
    (by rw [hkl]; exact repL_eltB (A2_check.2.2.2.1 lt2 hlA))
  rw [hkt] at hgeq
  have e : repA 1 = t0A := by simp [repA]
  rw [e] at hgeq
  exact c.iso.exists_conj_sup hg (v := t0B) hgeq

end Fus

section Cls

variable (c : AutCtx G M₁ M₂ z) (hZ : ZStmt c) (hT₀G : IsSylowTwoOf (c.iso.imgG That) ⊤)

include hZ hT₀G

theorem inv_conj_K {û : Bh} (hûT : (û : Ah) ∈ That) (hû2 : û * û = 1) (hû1 : (û : Ah) ≠ 1) :
    (∃ m ∈ (M₁ ⊔ M₂) ⊔ Subgroup.normalizer (c.iso.imgG A2h : Set G),
        m * c.iso.toG û * m⁻¹ = z) ∨
      (∃ m ∈ (M₁ ⊔ M₂) ⊔ Subgroup.normalizer (c.iso.imgG A2h : Set G),
        m * c.iso.toG û * m⁻¹ = c.iso.toG fhB) := by
  have hM : ∀ {m : G}, m ∈ M₁ ⊔ M₂ →
      m ∈ (M₁ ⊔ M₂) ⊔ Subgroup.normalizer (c.iso.imgG A2h : Set G) :=
    fun h => Subgroup.mem_sup_left h
  have hN : ∀ {m : G}, m ∈ Subgroup.normalizer (c.iso.imgG A2h : Set G) →
      m ∈ (M₁ ⊔ M₂) ⊔ Subgroup.normalizer (c.iso.imgG A2h : Set G) :=
    fun h => Subgroup.mem_sup_right h
  rcases inv_conj_M0 c hûT hû2 hû1 with ⟨m, hm, h⟩ | ⟨m, hm, h⟩ | ⟨m, hm, h⟩ | ⟨m, hm, h⟩
  · exact Or.inl ⟨m, hM hm, h⟩
  · exact Or.inr ⟨m, hM hm, h⟩
  · right
    obtain ⟨m₁, hm₁, h₁⟩ := yt_conj_t0 c
    obtain ⟨n, hn, hnF⟩ := exists_conj_F_yt c hZ hT₀G
    refine ⟨(m₁ * n)⁻¹ * m, Subgroup.mul_mem _ (Subgroup.inv_mem _
      (Subgroup.mul_mem _ (hM hm₁) (hN hn))) (hM hm), ?_⟩
    have hF : (m₁ * n)⁻¹ * c.iso.toG t0B * (m₁ * n) = c.iso.toG fhB := by
      rw [← h₁, ← hnF]
      group
    calc (m₁ * n)⁻¹ * m * c.iso.toG û * ((m₁ * n)⁻¹ * m)⁻¹
        = (m₁ * n)⁻¹ * (m * c.iso.toG û * m⁻¹) * (m₁ * n) := by group
      _ = c.iso.toG fhB := by rw [h, hF]
  · left
    obtain ⟨n, hn, hnz⟩ := exists_conj_z_Fz c hZ hT₀G
    refine ⟨n⁻¹ * m, Subgroup.mul_mem _ (Subgroup.inv_mem _ (hN hn)) (hM hm), ?_⟩
    calc n⁻¹ * m * c.iso.toG û * (n⁻¹ * m)⁻¹ = n⁻¹ * (m * c.iso.toG û * m⁻¹) * n := by group
      _ = z := by rw [h, ← hnz]; group

end Cls

end CFSG.Quasithin.H13.F431.U42Aut
