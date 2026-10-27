module

public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Chain
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Data

public section

namespace CFSG.Quasithin.H13.U3.GC137.S2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit
  CFSG.Quasithin.H13.G2Dat

theorem b₀_fix : act b₀ 8 = 8 := by
  unfold act
  rw [matCode_b₀]
  decide +kernel

theorem b₀_mem_Ppt : b₀ ∈ Ppt := mem_Ppt.2 b₀_fix

theorem sM_ne_bCode : ∀ i < 64, sM i ≠ bCode := by
  decide +kernel

theorem b₀_not_mem_S : b₀ ∉ sSubG := by
  intro h
  obtain ⟨i, hi, hib⟩ := mem_sSubG.1 h
  have := congrArg (fun g : Gam => matCode g.1) hib
  simp only [matCode_sEltG hi, matCode_b₀] at this
  exact sM_ne_bCode i hi this

theorem b₀_inv : b₀⁻¹ = b₀ * b₀ := by
  refine inv_eq_of_mul_eq_one_right (eq_of_code ?_)
  rw [matCode_mulG, matCode_mulG, matCode_b₀]
  exact b₀_checks.1.trans matCode_one.symm

@[expose] def Tset (g : Gam) : Prop :=
  g ∈ sSubG ∨ ∃ s ∈ sSubG, ∃ s' ∈ sSubG, g = s * b₀ * s'

theorem Tset.mul_left {g s : Gam} (h : Tset g) (hs : s ∈ sSubG) : Tset (s * g) := by
  rcases h with h | ⟨s₁, hs₁, s₂, hs₂, rfl⟩
  · exact Or.inl (mul_mem hs h)
  · exact Or.inr ⟨s * s₁, mul_mem hs hs₁, s₂, hs₂, by simp only [mul_assoc]⟩

theorem Tset.mul_right {g s : Gam} (h : Tset g) (hs : s ∈ sSubG) : Tset (g * s) := by
  rcases h with h | ⟨s₁, hs₁, s₂, hs₂, rfl⟩
  · exact Or.inl (mul_mem h hs)
  · exact Or.inr ⟨s₁, hs₁, s₂ * s, mul_mem hs₂ hs, by simp only [mul_assoc]⟩

theorem keyOk : ∀ i < 64,
    ((keyTab.getD i (0, 0, 0)).1 = 0 ∧ (keyTab.getD i (0, 0, 0)).2.1 < 64 ∧
      mmul (mmul bCode (sM i)) bCode = sM (keyTab.getD i (0, 0, 0)).2.1) ∨
    ((keyTab.getD i (0, 0, 0)).1 = 1 ∧ (keyTab.getD i (0, 0, 0)).2.1 < 64 ∧
      (keyTab.getD i (0, 0, 0)).2.2 < 64 ∧
      mmul (mmul bCode (sM i)) bCode = mmul (mmul (sM (keyTab.getD i (0, 0, 0)).2.1) bCode)
        (sM (keyTab.getD i (0, 0, 0)).2.2)) := by
  decide +kernel

theorem Tset_key {s : Gam} (hs : s ∈ sSubG) : Tset (b₀ * s * b₀) := by
  obtain ⟨i, hi, rfl⟩ := mem_sSubG.1 hs
  rcases keyOk i hi with ⟨-, hk, hc⟩ | ⟨-, hk, hl, hc⟩
  · refine Or.inl (mem_sSubG.2 ⟨_, hk, eq_of_code ?_⟩)
    simp only [matCode_sEltG hk, matCode_mulG, matCode_sEltG hi, matCode_b₀]
    exact hc.symm
  · refine Or.inr ⟨sEltG _, mem_sSubG.2 ⟨_, hk, rfl⟩, sEltG _, mem_sSubG.2 ⟨_, hl, rfl⟩,
      eq_of_code ?_⟩
    simp only [matCode_mulG, matCode_sEltG hi, matCode_b₀, matCode_sEltG hk, matCode_sEltG hl]
    exact hc

theorem Tset.mul {x y : Gam} (hx : Tset x) (hy : Tset y) : Tset (x * y) := by
  rcases hy with hy | ⟨s₃, hs₃, s₄, hs₄, rfl⟩
  · exact hx.mul_right hy
  · rcases hx with hx | ⟨s₁, hs₁, s₂, hs₂, rfl⟩
    · have hy' : Tset (s₃ * b₀ * s₄) := Or.inr ⟨s₃, hs₃, s₄, hs₄, rfl⟩
      exact hy'.mul_left hx
    · have := (Tset_key (mul_mem hs₂ hs₃)).mul_left hs₁ |>.mul_right hs₄
      simpa [mul_assoc] using this

theorem Tset_bb : Tset (b₀ * b₀) := by
  have := Tset_key (one_mem sSubG)
  simpa using this

theorem Tset.inv {x : Gam} (hx : Tset x) : Tset x⁻¹ := by
  rcases hx with hx | ⟨s₁, hs₁, s₂, hs₂, rfl⟩
  · exact Or.inl (inv_mem hx)
  · have := (Tset_bb.mul_left (inv_mem hs₂)).mul_right (inv_mem hs₁)
    simpa [mul_assoc, b₀_inv] using this

@[expose] def T0 : Subgroup Gam where
  carrier := {g | Tset g}
  mul_mem' := fun {_ _} hx hy => Tset.mul hx hy
  one_mem' := Or.inl (one_mem sSubG)
  inv_mem' := fun {_} hx => Tset.inv hx

theorem mem_T0 {g : Gam} : g ∈ T0 ↔ Tset g := Iff.rfl

theorem S_le_T0 : sSubG ≤ T0 := fun _ hs => Or.inl hs

theorem b₀_mem_T0 : b₀ ∈ T0 :=
  Or.inr ⟨1, one_mem sSubG, 1, one_mem sSubG, by simp⟩

theorem T0_le_Ppt : T0 ≤ Ppt := by
  intro g hg
  rcases hg with hg | ⟨s₁, hs₁, s₂, hs₂, rfl⟩
  · exact sSubG_le_Ppt hg
  · exact mul_mem (mul_mem (sSubG_le_Ppt hs₁) b₀_mem_Ppt) (sSubG_le_Ppt hs₂)

@[expose] def gl₁ : List Gam := [bgen 0, bgen 1, bgen 2, bgen 3]

theorem codes_gl₁ : (gl₁.map fun x => matCode x.1) = [matT01, matT10, matX, matTau] := by
  simp only [gl₁, List.map_cons, List.map_nil, matCode_bgen (by norm_num : 0 < 4),
    matCode_bgen (by norm_num : 1 < 4), matCode_bgen (by norm_num : 2 < 4),
    matCode_bgen (by norm_num : 3 < 4)]
  rfl

theorem chain_trans_ok : chainCovers [matT01, matT10, matX, matTau] chainTrans omegaL = true := by
  decide +kernel

theorem trans_pts : ∀ c ∈ omegaL, ∃ h : Gam, act h 8 = c := by
  intro c hc
  obtain ⟨h, -, hh⟩ := chainCovers_sound ⊤ gl₁ (fun _ _ => Subgroup.mem_top _) chainTrans omegaL
    (by rw [codes_gl₁]; exact chain_trans_ok) c hc
  exact ⟨h, hh⟩

theorem isPt_iff_mem : ∀ c ∈ o0Codes, isPt c = true → c ∈ omegaL := by
  decide +kernel

theorem card_isPt : (o0Codes.filter isPt).length = 63 := by
  decide +kernel

theorem orbit_pt0 : MulAction.orbit Gam pt0 = {c : O0C | isPt c.1 = true} := by
  ext c
  constructor
  · rintro ⟨g, rfl⟩
    exact isPt_act g (by decide) (by decide)
  · intro hc
    obtain ⟨h, hh⟩ := trans_pts c.1 (isPt_iff_mem c.1 c.2 hc)
    exact ⟨h, Subtype.ext hh⟩

theorem card_orbit_pt0 : Nat.card (MulAction.orbit Gam pt0) = 63 := by
  rw [orbit_pt0]
  exact (card_o0C_filter isPt).trans card_isPt

theorem card_orbit_mul_card_Ppt :
    Nat.card (MulAction.orbit Gam pt0) * Nat.card Ppt = Nat.card Gam := by
  classical
  have : Fintype Gam := Fintype.ofFinite Gam
  have : Fintype (MulAction.orbit Gam pt0) := Fintype.ofFinite _
  have : Fintype (MulAction.stabilizer Gam pt0) := Fintype.ofFinite _
  simp only [Ppt, Nat.card_eq_fintype_card]
  exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group Gam pt0

theorem card_Ppt : Nat.card Ppt = 192 := by
  have h := card_orbit_mul_card_Ppt
  rw [card_orbit_pt0, card_g2Two] at h
  omega

theorem card_T0 : Nat.card T0 = 192 := by
  have h1 : Nat.card sSubG ∣ Nat.card T0 := Subgroup.card_dvd_of_le S_le_T0
  have h2 : Nat.card T0 ∣ Nat.card Ppt := Subgroup.card_dvd_of_le T0_le_Ppt
  rw [card_sSubG] at h1
  rw [card_Ppt] at h2
  have hpos : 0 < Nat.card T0 := Nat.card_pos
  have hle : Nat.card T0 ≤ 192 := Nat.le_of_dvd (by norm_num) h2
  obtain ⟨k, hk⟩ := h1
  rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl
  · exfalso
    have hS : sSubG = T0 := Subgroup.eq_of_le_of_card_ge S_le_T0 (by rw [card_sSubG, hk])
    exact b₀_not_mem_S (hS ▸ b₀_mem_T0)
  · exfalso
    rw [hk] at h2
    norm_num at h2
  · omega

theorem T0_eq_Ppt : T0 = Ppt :=
  Subgroup.eq_of_le_of_card_ge T0_le_Ppt (by rw [card_T0, card_Ppt])

theorem mem_Ppt_iff {g : Gam} : g ∈ Ppt ↔ Tset g := by
  rw [← T0_eq_Ppt]
  exact mem_T0

end CFSG.Quasithin.H13.U3.GC137.S2
