module

public import CFSG.Quasithin.Vol2.GoldschmidtF48RigVeq
public import CFSG.Quasithin.Vol2.GoldschmidtF48RigDef
public import CFSG.Quasithin.Recognition.F4Basic

section

public section

namespace CFSG.Quasithin.H13.F48Rig

open CFSG.Quasithin

variable {N : Type*} [Group N]

theorem normalizer_le_of_complement {Q C H : Subgroup N} [hQ : Q.Normal]
    (hC : IsComplementIn C Q ⊤) (hHC : H ≤ C)
    (hfix : ∀ q ∈ Q, (∀ h ∈ H, h * q * h⁻¹ = q) → q = 1) {x : N}
    (hx : x ∈ Subgroup.normalizer (H : Set N)) : x ∈ C := by
  obtain ⟨q, hq, c, hc, rfl⟩ := hC.2.2.2 x (Subgroup.mem_top x)
  have hQC : ∀ y ∈ Q, y ∈ C → y = 1 := fun y hy hyC => by
    have : y ∈ Q ⊓ C := ⟨hy, hyC⟩
    rw [hC.2.2.1] at this
    exact this
  have hx' := Subgroup.mem_normalizer_iff.mp hx
  have hconj : ∀ h ∈ H, q * c * h * (q * c)⁻¹ = c * h * c⁻¹ := by
    intro h hh
    have h1 : q * c * h * (q * c)⁻¹ ∈ C := hHC ((hx' h).mp hh)
    have h2 : c * h * c⁻¹ ∈ C := C.mul_mem (C.mul_mem hc (hHC hh)) (C.inv_mem hc)
    have h3 : (c * h * c⁻¹)⁻¹ * (q * c * h * (q * c)⁻¹) ∈ Q := by
      have e : (c * h * c⁻¹)⁻¹ * (q * c * h * (q * c)⁻¹) =
          ((c * h * c⁻¹)⁻¹ * q * (c * h * c⁻¹)⁻¹⁻¹) * q⁻¹ := by group
      rw [e]
      exact Q.mul_mem (hQ.conj_mem q hq _) (Q.inv_mem hq)
    have := hQC _ h3 (C.mul_mem (C.inv_mem h2) h1)
    rw [inv_mul_eq_one] at this
    exact this.symm
  have hcn : c ∈ Subgroup.normalizer (H : Set N) := by
    refine Subgroup.mem_normalizer_iff.mpr fun h => ?_
    constructor
    · intro hh
      rw [← hconj h hh]
      exact (hx' h).mp hh
    · intro hh
      obtain ⟨n, hn⟩ : ∃ n : N, n = (q * c)⁻¹ * (c * h * c⁻¹) * (q * c) := ⟨_, rfl⟩
      have e : q * c * n * (q * c)⁻¹ = c * h * c⁻¹ := by rw [hn]; group
      have hnH : n ∈ H := (hx' n).mpr (by rw [e]; exact hh)
      have e1 := hconj n hnH
      rw [e] at e1
      have : n = h := mul_left_cancel (mul_right_cancel e1.symm)
      rw [← this]
      exact hnH
  have hqn : q ∈ Subgroup.normalizer (H : Set N) := by
    have := (Subgroup.normalizer (H : Set N)).mul_mem hx
      ((Subgroup.normalizer (H : Set N)).inv_mem hcn)
    simpa using this
  have hq' := Subgroup.mem_normalizer_iff.mp hqn
  have hq1 : q = 1 := by
    refine hfix q hq fun h hh => ?_
    have h1 : q * h * q⁻¹ ∈ H := (hq' h).mp hh
    have h2 : q * h * q⁻¹ * h⁻¹ ∈ H := H.mul_mem h1 (H.inv_mem hh)
    have h3 : q * h * q⁻¹ * h⁻¹ ∈ Q := by
      have e : q * h * q⁻¹ * h⁻¹ = q * (h * q⁻¹ * h⁻¹) := by group
      rw [e]
      exact Q.mul_mem hq (hQ.conj_mem q⁻¹ (Q.inv_mem hq) h)
    have h4 := hQC _ h3 (hHC h2)
    have h5 : q * h = h * q := mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h4)
    calc h * q * h⁻¹ = (q * h) * h⁻¹ := by rw [h5]
      _ = q := by group
  rw [hq1, one_mul]
  exact hc

theorem complement_unique {Q C C' G H : Subgroup N} [Q.Normal]
    (hC' : IsComplementIn C' Q ⊤) (hGC : G ≤ C) (hGC' : G ≤ C')
    (hmax : ∀ M : Subgroup N, G ≤ M → M ≤ C → M = G ∨ M = C)
    (hmax' : ∀ M : Subgroup N, G ≤ M → M ≤ C' → M = G ∨ M = C')
    (hHG : H ≤ G) (hfix : ∀ q ∈ Q, (∀ h ∈ H, h * q * h⁻¹ = q) → q = 1) {w : N} (hwC : w ∈ C)
    (hwG : w ∉ G) (hw : w ∈ Subgroup.normalizer (H : Set N)) : C = C' := by
  have hwC' : w ∈ C' := normalizer_le_of_complement hC' (hHG.trans hGC') hfix hw
  have hM : G ⊔ Subgroup.zpowers w ≤ C :=
    sup_le hGC ((Subgroup.zpowers_le).mpr hwC)
  have hM' : G ⊔ Subgroup.zpowers w ≤ C' :=
    sup_le hGC' ((Subgroup.zpowers_le).mpr hwC')
  have hne : G ≠ G ⊔ Subgroup.zpowers w := fun h =>
    hwG (h ▸ (le_sup_right : Subgroup.zpowers w ≤ G ⊔ _) (Subgroup.mem_zpowers w))
  have e1 : G ⊔ Subgroup.zpowers w = C :=
    (hmax _ le_sup_left hM).resolve_left hne.symm
  have e2 : G ⊔ Subgroup.zpowers w = C' :=
    (hmax' _ le_sup_left hM').resolve_left hne.symm
  rw [← e1, e2]

theorem maximal_of_twoTrans {X : Type*} [MulAction N X] {C G : Subgroup N} {S : Set X} {u : X}
    (hu : u ∈ S) (hS : ∀ g ∈ C, ∀ x ∈ S, g • x ∈ S)
    (h2 : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, a ≠ b → c ≠ d →
      ∃ g ∈ C, g • a = c ∧ g • b = d)
    (hG : ∀ g ∈ C, g ∈ G ↔ g • u = u) :
    ∀ M : Subgroup N, G ≤ M → M ≤ C → M = G ∨ M = C := by
  intro M hGM hMC
  by_cases hMG : M ≤ G
  · exact Or.inl (le_antisymm hMG hGM)
  right
  obtain ⟨m, hm, hmG⟩ := Set.not_subset.mp hMG
  have hmu : m • u ≠ u := fun h => hmG ((hG m (hMC hm)).mpr h)
  refine le_antisymm hMC fun c hc => ?_
  by_cases hcu : c • u = u
  · exact hGM ((hG c hc).mpr hcu)
  · obtain ⟨g, hgC, hg1, hg2⟩ := h2 u hu (m • u) (hS m (hMC hm) u hu) u hu (c • u)
      (hS c hc u hu) (Ne.symm hmu) (Ne.symm hcu)
    have hgM : g ∈ M := hGM ((hG g hgC).mpr hg1)
    have hk : (c⁻¹ * (g * m)) • u = u := by
      rw [mul_smul, mul_smul, hg2, ← mul_smul, inv_mul_cancel, one_smul]
    have hkM : c⁻¹ * (g * m) ∈ M :=
      hGM ((hG _ (C.mul_mem (C.inv_mem hc) (C.mul_mem hgC (hMC hm)))).mpr hk)
    have e : c = (g * m) * (c⁻¹ * (g * m))⁻¹ := by group
    rw [e]
    exact M.mul_mem (M.mul_mem hgM hm) (M.inv_mem hkM)

end CFSG.Quasithin.H13.F48Rig

end

end

public section

namespace CFSG.Quasithin.H13.F48Rig

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

universe u

section Nbrs

variable {α : RankTwoAmalgam.{u}} {Y : Type} [Group Y]

theorem exists_f1_smul_lv (c : α.Completion Y) {v : c.Γ} (hv : c.graph.Adj c.xv v) :
    ∃ a : α.G1, f1 (c := c) a • c.lv = v := by
  obtain ⟨g, hg1, hg2⟩ := CosetGeom.exists_stab_smul_eq CosetGeom.adj_γ₀_γ₁ hv
  obtain ⟨a, rfl⟩ := stv_xv_le_range_f1 c (MulAction.mem_stabilizer_iff.mpr hg1)
  exact ⟨a, hg2⟩

theorem maximal_inf_range (c : α.Completion Y) (hc : c.IsFaithful) {C : Subgroup α.G1}
    (h2 : ∀ u₁ u₂ u₃ u₄ : c.Γ, c.graph.Adj c.xv u₁ → c.graph.Adj c.xv u₂ →
      c.graph.Adj c.xv u₃ → c.graph.Adj c.xv u₄ → u₁ ≠ u₂ → u₃ ≠ u₄ →
      ∃ a ∈ C, f1 (c := c) a • u₁ = u₃ ∧ f1 (c := c) a • u₂ = u₄) :
    ∀ M : Subgroup α.G1, C ⊓ α.α1.range ≤ M → M ≤ C → M = C ⊓ α.α1.range ∨ M = C := by
  let _ : MulAction α.G1 c.Γ := MulAction.compHom c.Γ (f1 (c := c))
  refine maximal_of_twoTrans (S := {v | c.graph.Adj c.xv v}) (u := c.lv)
    CosetGeom.adj_γ₀_γ₁ ?_ ?_ ?_
  · intro g _ v hv
    have := (CosetGeom.smul_adj (f1 (c := c) g)).mpr hv
    rwa [f1_smul_xv] at this
  · intro v₁ h₁ v₂ h₂ v₃ h₃ v₄ h₄ hne₁ hne₂
    exact h2 v₁ v₂ v₃ v₄ h₁ h₂ h₃ h₄ hne₁ hne₂
  · intro g hg
    show _ ↔ f1 (c := c) g • c.lv = c.lv
    rw [f1_smul_lv_iff c hc g, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩

end Nbrs

section Cartan

variable {S : LieSetting.{u, 0}}

theorem cartan_at_lv (hT : S.CartanFPF) :
    ∃ b v : S.ι.Γ, S.ι.graph.dist S.ι.xv b = S.m ∧ S.ι.graph.Adj S.ι.xv v ∧ v ≠ S.ι.lv ∧
      ∃ h : S.ι.G0, h • S.ι.xv = S.ι.xv ∧ h • b = b ∧ h • S.ι.lv = S.ι.lv ∧ h • v = v ∧
        ∀ q ∈ S.Qbar S.ι.xv, h * q * h⁻¹ = q → q = 1 := by
  obtain ⟨b, u₁, u₂, hb, h₁, h₂, hne, h, hhx, hhb, hh1, hh2, hfix⟩ := hT
  obtain ⟨a, ha⟩ := exists_f1_smul_lv S.ι h₁
  set g : S.ι.G0 := f1 (c := S.ι) a with hg
  have hgx : g • S.ι.xv = S.ι.xv := f1_smul_xv a
  have hgx' : g⁻¹ • S.ι.xv = S.ι.xv := inv_smul_eq_iff.mpr hgx.symm
  have hgl : g • S.ι.lv = u₁ := ha
  refine ⟨g⁻¹ • b, g⁻¹ • u₂, ?_, ?_, ?_, g⁻¹ * h * g, ?_, ?_, ?_, ?_, ?_⟩
  · have := CosetGeom.dist_smul g⁻¹ S.ι.xv b
    rw [hgx'] at this
    rw [CosetGeom.dist] at this
    rw [← hb]
    exact this
  · have := (CosetGeom.smul_adj g⁻¹).mpr h₂
    rwa [hgx'] at this
  · intro heq
    apply hne
    rw [← hgl, ← heq, smul_inv_smul]
  · rw [mul_smul, mul_smul, hgx, hhx, hgx']
  · rw [mul_smul, mul_smul, smul_inv_smul, hhb]
  · rw [mul_smul, mul_smul, hgl, hh1]
    exact inv_smul_eq_iff.mpr hgl.symm
  · rw [mul_smul, mul_smul, smul_inv_smul, hh2]
  · intro q hq hqc
    have hgm : g ∈ stv S.ι S.ι.xv := MulAction.mem_stabilizer_iff.mpr hgx
    have hq' : g * q * g⁻¹ ∈ S.Qbar S.ι.xv := by
      have := mul_mem_conjSub (g := g) hq
      rwa [S.conjSub_Qbar hgm] at this
    have hc : h * (g * q * g⁻¹) * h⁻¹ = g * q * g⁻¹ :=
      calc h * (g * q * g⁻¹) * h⁻¹ = g * (g⁻¹ * h * g * q * (g⁻¹ * h * g)⁻¹) * g⁻¹ := by group
        _ = g * q * g⁻¹ := by rw [hqc]
    have h1 : g * q * g⁻¹ = 1 := hfix _ hq' hc
    calc q = g⁻¹ * (g * q * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group

end Cartan

section Main

variable {S : LieSetting.{u, 0}} {Y : Type} [Group Y] [Finite Y] (hS : S.Facts45L)
  (β : S.α.Completion Y) (hβ : β.IsFaithful) (hs : β.IsSmall S.m)

theorem mem_Cz_iff_of_mem_range {a : S.α.G1} (ha : a ∈ S.α.α1.range)
    (z : Vs β (decide (Odd S.m))) :
    a ∈ Cz β z.1 ↔ a ∈ Cz S.ι (vEq hS β hβ hs z).1 := by
  rw [mem_Cz, mem_Cz]
  have h1 := vEq_B1 hS β hβ hs ha z
  constructor
  · intro h
    have e : f1 (c := β) a • z = z := Subtype.ext h
    have h2 : f1 (c := S.ι) a • vEq hS β hβ hs z = vEq hS β hβ hs z := by rw [← h1, e]
    exact congrArg Subtype.val h2
  · intro h
    have h2 : vEq hS β hβ hs (f1 (c := β) a • z) = vEq hS β hβ hs z := by
      rw [h1]
      exact Subtype.ext h
    exact congrArg Subtype.val ((vEq hS β hβ hs).injective h2)

theorem Cz_inf_range (z : Vs β (decide (Odd S.m))) :
    Cz S.ι (vEq hS β hβ hs z).1 ⊓ S.α.α1.range = Cz β z.1 ⊓ S.α.α1.range := by
  ext a
  simp only [Subgroup.mem_inf]
  exact ⟨fun h => ⟨(mem_Cz_iff_of_mem_range hS β hβ hs h.2 z).mpr h.1, h.2⟩,
    fun h => ⟨(mem_Cz_iff_of_mem_range hS β hβ hs h.2 z).mp h.1, h.2⟩⟩

theorem Cz_eq_of_cartan {z : Vs β (decide (Odd S.m))} (hz : β.graph.dist β.xv z.1 = S.m)
    {u : S.ι.Γ} (hu : S.ι.graph.Adj S.ι.xv u) (hul : u ≠ S.ι.lv) {h : S.ι.G0}
    (hhx : h • S.ι.xv = S.ι.xv) (hhb : h • (vEq hS β hβ hs z).1 = (vEq hS β hβ hs z).1)
    (hhl : h • S.ι.lv = S.ι.lv) (hhu : h • u = u)
    (hfix : ∀ q ∈ S.Qbar S.ι.xv, h * q * h⁻¹ = q → q = 1) :
    Cz β z.1 = Cz S.ι (vEq hS β hβ hs z).1 ∧ ∃ w ∈ Cz β z.1, w ∉ S.α.α1.range := by
  have : S.Qb1.Normal := S.Qb1_normal
  have hzb : S.ι.graph.dist S.ι.xv (vEq hS β hβ hs z).1 = S.m := (vEq_far_iff hS β hβ hs z).mpr hz
  obtain ⟨hCβ, h2β⟩ := far_structure hS β hβ hs hz
  obtain ⟨-, h2ι⟩ := far_structure hS S.ι S.hι hS.isSmall_iota hzb
  have hGeq := Cz_inf_range hS β hβ hs z
  have hmaxι := maximal_inf_range S.ι S.hι h2ι
  have hmaxβ := maximal_inf_range β hβ h2β
  rw [← hGeq] at hmaxβ
  set H : Subgroup S.α.G1 := (Cz S.ι (vEq hS β hβ hs z).1 ⊓ S.α.α1.range) ⊓
    (stv S.ι u).comap (f1 (c := S.ι)) with hH
  have hfixQ : ∀ q ∈ S.Qb1, (∀ k ∈ H, k * q * k⁻¹ = q) → q = 1 := by
    intro q hq hk
    obtain ⟨a, rfl⟩ := stv_xv_le_range_f1 S.ι (MulAction.mem_stabilizer_iff.mpr hhx)
    have haH : a ∈ H := ⟨⟨hhb, (f1_smul_lv_iff S.ι S.hι a).mp hhl⟩, hhu⟩
    have e := congrArg (f1 (c := S.ι)) (hk a haH)
    rw [map_mul, map_mul, map_inv] at e
    exact f1_injective S.ι S.hι ((hfix _ hq e).trans (map_one _).symm)
  obtain ⟨w, hwC, hw1, hw2⟩ := h2ι S.ι.lv u u S.ι.lv CosetGeom.adj_γ₀_γ₁ hu hu
    CosetGeom.adj_γ₀_γ₁ (Ne.symm hul) hul
  have hwB : w ∉ S.α.α1.range := fun hw =>
    hul (hw1.symm.trans ((f1_smul_lv_iff S.ι S.hι w).mpr hw))
  have hconj : ∀ w' ∈ Cz S.ι (vEq hS β hβ hs z).1, f1 (c := S.ι) w' • S.ι.lv = u →
      f1 (c := S.ι) w' • u = S.ι.lv → ∀ a ∈ H, w' * a * w'⁻¹ ∈ H := by
    intro w' hw' e1 e2 a ha
    obtain ⟨⟨haC, haB⟩, hau⟩ := ha
    have hal : f1 (c := S.ι) a • S.ι.lv = S.ι.lv := (f1_smul_lv_iff S.ι S.hι a).mpr haB
    have hau' : f1 (c := S.ι) a • u = u := MulAction.mem_stabilizer_iff.mp hau
    have i1 : f1 (c := S.ι) w'⁻¹ • S.ι.lv = u := by
      rw [map_inv, inv_smul_eq_iff]
      exact e2.symm
    have i2 : f1 (c := S.ι) w'⁻¹ • u = S.ι.lv := by
      rw [map_inv, inv_smul_eq_iff]
      exact e1.symm
    have hB' : w' * a * w'⁻¹ ∈ S.α.α1.range := by
      rw [← f1_smul_lv_iff S.ι S.hι, map_mul, map_mul, mul_smul, mul_smul, i1, hau', e2]
    have hu' : w' * a * w'⁻¹ ∈ (stv S.ι u).comap (f1 (c := S.ι)) := by
      show f1 (c := S.ι) (w' * a * w'⁻¹) ∈ stv S.ι u
      rw [MulAction.mem_stabilizer_iff, map_mul, map_mul, mul_smul, mul_smul, i2, hal, e1]
    exact ⟨⟨(Cz S.ι _).mul_mem ((Cz S.ι _).mul_mem hw' haC) ((Cz S.ι _).inv_mem hw'), hB'⟩, hu'⟩
  have hswap1 : f1 (c := S.ι) w⁻¹ • S.ι.lv = u := by
    rw [map_inv, inv_smul_eq_iff]
    exact hw2.symm
  have hswap2 : f1 (c := S.ι) w⁻¹ • u = S.ι.lv := by
    rw [map_inv, inv_smul_eq_iff]
    exact hw1.symm
  have hwN : w ∈ Subgroup.normalizer (H : Set S.α.G1) := by
    refine Subgroup.mem_normalizer_iff.mpr fun a =>
      ⟨fun ha => hconj w hwC hw1 hw2 a ha, fun ha => ?_⟩
    have := hconj w⁻¹ ((Cz S.ι _).inv_mem hwC) hswap1 hswap2 _ ha
    rwa [show w⁻¹ * (w * a * w⁻¹) * w⁻¹⁻¹ = a by group] at this
  have hCeq : Cz S.ι (vEq hS β hβ hs z).1 = Cz β z.1 :=
    complement_unique (Q := S.Qb1) (G := Cz S.ι (vEq hS β hβ hs z).1 ⊓ S.α.α1.range) (H := H) hCβ
      inf_le_left (hGeq.le.trans inf_le_left) hmaxι hmaxβ inf_le_left hfixQ hwC
      (fun hwG => hwB hwG.2) hwN
  exact ⟨hCeq.symm, w, by rw [← hCeq]; exact hwC, hwB⟩

theorem exists_far_data (hT : S.CartanFPF) :
    ∃ z : Vs β (decide (Odd S.m)), β.graph.dist β.xv z.1 = S.m ∧
      Cz β z.1 = Cz S.ι (vEq hS β hβ hs z).1 ∧ ∃ w ∈ Cz β z.1, w ∉ S.α.α1.range := by
  obtain ⟨b, v, hb, hv, hvl, h, hhx, hhb, hhl, hhv, hfix⟩ := cartan_at_lv hT
  let zb : Vs S.ι (decide (Odd S.m)) := ⟨b, vtype_of_dist_xv S.ι hb⟩
  let z : Vs β (decide (Odd S.m)) := (vEq hS β hβ hs).symm zb
  have hzz : vEq hS β hβ hs z = zb := (vEq hS β hβ hs).apply_symm_apply zb
  have hfar : β.graph.dist β.xv z.1 = S.m := (vEq_far_iff hS β hβ hs z).mp (by rw [hzz]; exact hb)
  have hhb' : h • (vEq hS β hβ hs z).1 = (vEq hS β hβ hs z).1 := by rw [hzz]; exact hhb
  exact ⟨z, hfar, Cz_eq_of_cartan hS β hβ hs hfar hv hvl hhx hhb' hhl hhv hfix⟩

end Main

end CFSG.Quasithin.H13.F48Rig
